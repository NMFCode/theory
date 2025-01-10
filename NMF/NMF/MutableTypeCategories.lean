import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

open CategoryTheory

namespace MutableTypeCategories

universe u


/-
# General mutable type category definitions
-/

variable (Ω : Type u)
@[simp]
abbrev morph (A B : Type u) : Type u := (A×Ω) → (B×Ω)

@[simp]
abbrev comp {A B C : Type u} (f : morph Ω A B) (g : morph Ω B C) : morph Ω A C
  := g ∘ f

@[simp]
def side_effect_free {A B : Type u} {Ω : Type u} (f : morph Ω A B) : Prop
 := ∀ a : A × Ω, (f a).snd = a.snd

@[simp]
def stateless {A B : Type u} {Ω : Type u} (f : morph Ω A B) : Prop
 := ∀ a : A, ∀ ω : Ω, ∀ ω2 : Ω, (f (a,ω)).1 = (f (a,ω2)).1

@[simp]
def id_morph (A : Type u) : morph Ω A A
 := @id (A × Ω)

lemma id_sef (A : Type u) : side_effect_free (id_morph Ω A) := by
  simp

lemma id_stateless (A : Type u) : stateless (id_morph Ω A) := by simp

lemma comp_side_effect_free {A B C : Type u} {Ω : Type u} (f : morph Ω A B) (g : morph Ω B C)
  : side_effect_free f ∧ side_effect_free g → side_effect_free (comp Ω f g)
  := by intro H; rw[side_effect_free]; intro a; rw[comp]; simp; rw [H.right, H.left]

instance MutableTypeCategory : Category.{u} (Type u) where
  Hom A B := morph Ω A B
  id A := id_morph Ω A
  comp f g := g ∘ f

structure SideEffectFreeMorphism {Ω : Type u} (A B : Type u) where
  m : morph Ω A B
  proof : side_effect_free m

instance SideEffectFreeMutableTypeCategory : Category.{u} (Type u) where
  Hom A B := SideEffectFreeMorphism A B
  id A := { m:= id_morph Ω A, proof:= id_sef Ω A}
  comp f g := {
    m := g.m ∘ f.m
    proof := comp_side_effect_free f.m g.m (And.intro f.proof g.proof)
  }

/-
# Lazy Collections
-/

open Finset
open Multiset
open Set
open List

structure LazyCollection (T : Type u → Type u) (A : Type u) where
  eval : Ω → T A

abbrev LazyPowerset (A : Type u) := LazyCollection Ω Finset A

abbrev LazyMultiset (A : Type u) := LazyCollection Ω Multiset A

abbrev LazyList (A : Type u) := LazyCollection Ω List A

abbrev LazySet (A : Type u) := LazyCollection Ω Set A

@[simp]
def lazy_set_func {A B : Type u} (f : morph Ω A B) : morph Ω (LazySet Ω A) (LazySet Ω B) :=
  fun (s : (LazySet Ω A) × Ω) => ({
    eval:= fun (ω : Ω) => { b : B | ∃ a, a ∈ (s.1.eval ω) ∧ b = (f (a, ω)).1 }
  }, s.2)

@[simp]
def lazy_powerset_func {A B : Type u} (f : morph Ω A B) [DecidableEq B] : morph Ω (LazyPowerset Ω A) (LazyPowerset Ω B) :=
  fun (s : (LazyPowerset Ω A) × Ω) => ({
    eval:= fun (ω : Ω) =>
    let m := (s.1.eval ω).val.map (fun (a : A) => (f (a,ω)).1)
    {
      val := m.dedup
      nodup := Multiset.dedup_eq_self.mp m.dedup_idem
    }
  }, s.2)

@[simp]
def lazy_multiset_func {A B : Type u} (f : morph Ω A B) : morph Ω (LazyMultiset Ω A) (LazyMultiset Ω B) :=
  fun (s : (LazyMultiset Ω A) × Ω) => ({
    eval:= fun (ω : Ω) => (s.1.eval ω).map (fun (a : A) => (f (a,ω)).1)
  }, s.2)

@[simp]
def lazy_list_func {A B : Type u} (f : morph Ω A B) : morph Ω (LazyList Ω A) (LazyList Ω B) :=
  fun (s : (LazyList Ω A) × Ω) => ({
    eval:= fun (ω : Ω) => (s.1.eval ω).map (fun (a : A) => (f (a,ω)).1)
  }, s.2)

@[simp]
def lift_set_lazy {A Ω : Type u} (set : Set A) : LazySet Ω A
  := {
    eval := fun (_ : Ω) => set
  }

@[simp]
def lift_list_lazy {A Ω : Type u} (list : List A) : LazyList Ω A
  := {
    eval := fun (_ : Ω) => list
  }

lemma lazy_set_func_sideeffect_free {A B : Type u} (f : morph Ω A B) :
  side_effect_free (lazy_set_func Ω f)
  := by simp

lemma lazy_powerset_func_sideeffect_free {A B : Type u} [DecidableEq B] (f : morph Ω A B) :
  side_effect_free (lazy_powerset_func Ω f)
  := by simp

lemma lazy_multiset_func_sideeffect_free {A B : Type u} (f : morph Ω A B) :
  side_effect_free (lazy_multiset_func Ω f)
  := by simp

lemma lazy_list_func_sideeffect_free {A B : Type u} (f : morph Ω A B) :
  side_effect_free (lazy_list_func Ω f)
  := by simp

@[simp]
def unit_lazy_set { A B : Type u} (f : morph Ω A B) : morph Ω A (LazySet Ω B)
  := fun (a,ω2) => ({
    eval := fun ω => { (f (a,ω)).1 }
  }, ω2)

@[simp]
def unit_lazy_multiset { A B : Type u} (f : morph Ω A B) : morph Ω A (LazyMultiset Ω B)
  := fun (a,ω2) => ({
    eval := fun ω => { (f (a,ω)).1 }
  }, ω2)

@[simp]
def unit_lazy_powerset { A B : Type u} (f : morph Ω A B) : morph Ω A (LazyPowerset Ω B)
  := fun (a,ω2) => ({
    eval := fun ω => { (f (a,ω)).1 }
  }, ω2)

@[simp]
def unit_lazy_list { A B : Type u} (f : morph Ω A B) : morph Ω A (LazyList Ω B)
  := fun (a,ω2) => ({
    eval := fun ω => [ (f (a,ω)).1 ]
  }, ω2)

structure OrderedSet (A : Type u) where
  items : List A
  nodup : Nodup items

structure LazyOrderedSet (A : Type u) where
  eval : Ω → OrderedSet A

/-
# Synchronization block theory and lenses
-/

structure Lens (Ω : Type u) (A B : Type u) where
  get : morph Ω A B
  put : morph Ω (A × B) A
  get_side_effect_free : side_effect_free get

@[simp]
def put_get (f : Lens Ω A B) :=
  ∀ a : A×Ω, f.put ((a.fst, (f.get a).fst), a.snd) = a

@[simp]
def get_put (f : Lens Ω A B) :=
  ∀ a : A, ∀ ω : Ω, ∀ b : B, ∃ a2 : A, ∃ ω2 : Ω, f.put ((a,b), ω) = (a2,ω2) ∧ f.get (a2, ω2) = (b,ω2)

@[simp]
def well_behaved (f : Lens Ω A B) := put_get Ω f ∧ get_put Ω f

@[simp]
def persistent (f : Lens Ω A B) := ∀ a : A, ∀ b : B, ∀ ω : Ω, (f.put ((a,b),ω)).fst = a

@[simp]
def transient (f : Lens Ω A B) := side_effect_free f.put ∧ stateless f.get

def Lens.comp {A B C : Type u} (f : Lens Ω A B) (g : Lens Ω B C) : Lens Ω A C
  := {
    get := g.get ∘ f.get
    put := fun a =>
      let gput := g.put (((f.get (a.fst.fst, a.snd)).fst, a.fst.snd), a.snd)
      f.put ((a.fst.fst, gput.fst), gput.snd)
    get_side_effect_free := by
      rw [side_effect_free]
      intro a
      simp
      rw [g.get_side_effect_free, f.get_side_effect_free]
  }

theorem comp_wellbehaved_putget { A B C : Type u} (f : Lens Ω A B) (g : Lens Ω B C) :
  well_behaved Ω f ∧ well_behaved Ω g → put_get Ω (Lens.comp Ω f g) := by
  intro H
  have f_wellbehaved : well_behaved Ω f := H.left
  have g_wellbehaved : well_behaved Ω g := H.right
  rw [put_get]
  intro a
  rw [Lens.comp]
  simp
  have g_putget := g_wellbehaved.left (f.get a)
  have hSimpleF : (f.get a).2 = a.2 := by
    rw[f.get_side_effect_free]
  rw[hSimpleF] at g_putget
  rw[g_putget]
  have f_putget := f_wellbehaved.left a
  rw [← hSimpleF] at f_putget
  exact f_putget

theorem comp_transient_wellbehaved { A B C : Type u} (f : Lens Ω A B) (g : Lens Ω B C) :
  well_behaved Ω f ∧ well_behaved Ω g ∧ transient Ω g → well_behaved Ω (Lens.comp Ω f g) := by
  intro H
  have f_wellbehaved : well_behaved Ω f := H.left
  have g_wellbehaved : well_behaved Ω g := H.right.left
  have g_transient := H.right.right
  rw[transient,side_effect_free] at g_transient
  apply And.intro
  exact comp_wellbehaved_putget Ω f g (And.intro f_wellbehaved g_wellbehaved)
  rw [get_put]
  intro a ω c
  rw [Lens.comp]
  simp
  have g_getput := g_wellbehaved.right (f.get (a,ω)).1 ω c
  obtain ⟨b, ht⟩ := g_getput
  obtain ⟨ω2, ha2⟩ := ht
  have hOmegasEqual := g_transient.left (((f.get (a, ω)).1, c),ω)
  rw[ha2.left] at hOmegasEqual
  simp at hOmegasEqual
  rw [hOmegasEqual] at ha2
  rw[ha2.left]
  simp
  have f_getput := f_wellbehaved.right a ω b
  obtain ⟨a2,ht⟩ := f_getput
  obtain ⟨ω3,ha3⟩ := ht
  use a2
  use ω3
  apply And.intro
  exact ha3.left
  rw[ha3.right]
  have hb := g_transient.right b ω3 ω
  rw[ha2.right] at hb
  simp at hb
  have ho := g.get_side_effect_free (b,ω3)
  simp at ho
  rw[←hb]
  nth_rewrite 3 [← ho]
  simp

/-
# Synchronization blocks
-/

structure SynchronizationBlock (ΩL ΩR A B C D : Type u) where
  f : Lens ΩL A B
  g : Lens ΩR C D
  Φbase : A ≃ C
  Φinh : B ≃ D
  f_persistent : persistent ΩL f
  g_persistent : persistent ΩR g
  f_wellbehaved : well_behaved ΩL f
  g_wellbehaved : well_behaved ΩR g

@[simp]
def consistent {ΩL ΩR A B C D : Type u} (s : SynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
  := s.Φinh (s.f.get (a,ωL)).1 = (s.g.get (c,ωR)).1

@[simp]
def repair_right {ΩL ΩR A B C D : Type u} (s : SynchronizationBlock ΩL ΩR A B C D) (a : A) (c : C) (ωL : ΩL) (ωR : ΩR)
  := (s.g.put ((c, s.Φinh (s.f.get (a,ωL)).1), ωR)).2

@[simp]
def repair_left {ΩL ΩR A B C D : Type u} (s : SynchronizationBlock ΩL ΩR A B C D) (a : A) (c : C) (ωL : ΩL) (ωR : ΩR)
  := (s.f.put ((a, s.Φinh.symm (s.g.get (c,ωR)).1), ωL)).2

theorem right_repair_repairs_inconsistency {ΩL ΩR A B C D : Type u} (s : SynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
  : consistent s ωL (repair_right s a c ωL ωR) a c
  := by
  simp
  have h_comega_cancels_out := s.g_persistent c (s.Φinh (s.f.get (a, ωL)).1) ωR
  have h_simplifyput : (c, (s.g.put ((c, s.Φinh (s.f.get (a, ωL)).1), ωR)).2) = (s.g.put ((c, s.Φinh (s.f.get (a, ωL)).1), ωR)) :=
   by
   rw[Prod.mk_inj_right]
   symm
   exact h_comega_cancels_out
  rw[h_simplifyput]
  have g_getput := s.g_wellbehaved.right c ωR (s.Φinh (s.f.get (a, ωL)).1)
  obtain ⟨a2, ht⟩ := g_getput
  obtain ⟨ω2,ha2⟩ := ht
  rw[ha2.left,ha2.right]

theorem left_repair_repairs_inconsistency {ΩL ΩR A B C D : Type u} (s : SynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
  : consistent s (repair_left s a c ωL ωR) ωR a c
  := by
  simp
  have h_comega_cancels_out := s.f_persistent a (s.Φinh.invFun (s.g.get (c, ωR)).1) ωL
  have h_simplifyput : (a, (s.f.put ((a, s.Φinh.symm (s.g.get (c, ωR)).1), ωL)).2) = (s.f.put ((a, s.Φinh.symm (s.g.get (c, ωR)).1), ωL)) :=
   by
   rw[Prod.mk_inj_right]
   symm
   exact h_comega_cancels_out
  rw[h_simplifyput]
  have f_getput := s.f_wellbehaved.right a ωL (s.Φinh.symm (s.g.get (c, ωR)).1)
  obtain ⟨c2, ht⟩ := f_getput
  obtain ⟨ω2,hc2⟩ := ht
  rw[hc2.left,hc2.right]
  simp

theorem right_repair_hippocratic {ΩL ΩR A B C D : Type u} (s : SynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
  : consistent s ωL ωR a c → (repair_right s a c ωL ωR) = ωR
  := by
  simp
  intro hc
  rw[hc]
  have g_putget := s.g_wellbehaved.left (c,ωR)
  simp at g_putget
  rw[g_putget]

theorem left_repair_hippocratic {ΩL ΩR A B C D : Type u} (s : SynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
  : consistent s ωL ωR a c → (repair_left s a c ωL ωR) = ωL
  := by
  simp
  intro ha
  rw[← Equiv.eq_symm_apply] at ha
  rw[← ha]
  have f_putget := s.f_wellbehaved.left (a,ωL)
  simp at f_putget
  rw[f_putget]

/-
# Collection-valued synchronization blocks
-/

structure LazyMutableCollection (T : Type u → Type u) (A : Type u) extends LazyCollection Ω T A where
  apply : Ω → T A → Ω

abbrev LazyPowersetCollection (A : Type u) := LazyMutableCollection Ω Finset A

abbrev LazyMultisetCollection (A : Type u) := LazyMutableCollection Ω Multiset A

abbrev LazyListCollection (A : Type u) := LazyMutableCollection Ω List A

abbrev LazySetCollection (A : Type u):= LazyMutableCollection Ω Set A

@[simp]
def eval_apply_collection {A Ω : Type u} {T : Type u → Type u} (c : LazyMutableCollection Ω T A) : Prop
  := ∀ ω : Ω, ∀ s : T A, c.eval (c.apply ω s) = s

@[simp]
def apply_eval_collection {A Ω : Type u} {T : Type u → Type u} (c : LazyMutableCollection Ω T A) : Prop
  := ∀ ω : Ω, c.apply ω (c.eval ω) = ω

structure WellBehavedMutableCollection (Ω A : Type u) (T : Type u → Type u)  where
  items : LazyMutableCollection Ω T A
  eval_apply : eval_apply_collection items
  apply_eval : apply_eval_collection items

structure LazyMutableCollectionSynchronizationBlock (ΩL ΩR A B C D : Type u) (T : Type u → Type u) where
  f : morph ΩL A (WellBehavedMutableCollection ΩL B T)
  g : morph ΩR C (WellBehavedMutableCollection ΩR D T)
  Φbase : A ≃ C
  Φinh : T B ≃ T D
  f_stateless : stateless f
  g_stateless : stateless g

@[simp]
def consistent_collection {ΩL ΩR A B C D : Type u} {T : Type u → Type u}
  (s : LazyMutableCollectionSynchronizationBlock ΩL ΩR A B C D T) (a : A) (c : C) (ωL : ΩL) (ωR : ΩR)
  : Prop
  := s.Φinh ((s.f (a,ωL)).1.items.eval ωL) = (s.g (c,ωR)).1.items.eval ωR

@[simp]
def repair_right_collection {ΩL ΩR A B C D : Type u} {T : Type u → Type u}
  (s : LazyMutableCollectionSynchronizationBlock ΩL ΩR A B C D T) (a : A) (c : C) (ωL : ΩL) (ωR : ΩR)
  : ΩR
  := (s.g (c,ωR)).1.items.apply ωR (s.Φinh ((s.f (a,ωL)).1.items.eval ωL))

@[simp]
def repair_left_collection {ΩL ΩR A B C D : Type u} {T : Type u → Type u}
  (s : LazyMutableCollectionSynchronizationBlock ΩL ΩR A B C D T) (a : A) (c : C) (ωL : ΩL) (ωR : ΩR)
  : ΩL
  := (s.f (a,ωL)).1.items.apply ωL (s.Φinh.invFun ((s.g (c,ωR)).1.items.eval ωR))

theorem repair_right_collection_repairs_inconsistency {ΩL ΩR A B C D : Type u} {T : Type u → Type u}
  (s : LazyMutableCollectionSynchronizationBlock ΩL ΩR A B C D T) (a : A) (c : C) (ωL : ΩL) (ωR : ΩR)
  : consistent_collection s a c ωL (repair_right_collection s a c ωL ωR)
  := by
     simp
     have h_g_stateless : (s.g (c, (s.g (c, ωR)).1.items.apply ωR (s.Φinh ((s.f (a, ωL)).1.items.eval ωL)))).1 = (s.g (c,ωR)).1
        := by
           exact s.g_stateless c ((s.g (c, ωR)).1.items.apply ωR (s.Φinh ((s.f (a, ωL)).1.items.eval ωL))) ωR
     rw [h_g_stateless]
     rw [(s.g (c, ωR)).1.eval_apply ωR (s.Φinh ((s.f (a, ωL)).1.items.eval ωL))]

theorem repair_left_collection_repairs_inconsistency {ΩL ΩR A B C D : Type u} {T : Type u → Type u}
  (s : LazyMutableCollectionSynchronizationBlock ΩL ΩR A B C D T) (a : A) (c : C) (ωL : ΩL) (ωR : ΩR)
  : consistent_collection s a c (repair_left_collection s a c ωL ωR) ωR
  := by
     simp
     have h_f_stateless : (s.f (a, (s.f (a, ωL)).1.items.apply ωL (s.Φinh.symm ((s.g (c, ωR)).1.items.eval ωR)))).1 = (s.f (a,ωL)).1
        := by
           exact s.f_stateless a ((s.f (a, ωL)).1.items.apply ωL (s.Φinh.symm ((s.g (c, ωR)).1.items.eval ωR))) ωL
     rw [h_f_stateless]
     rw [(s.f (a, ωL)).1.eval_apply ωL (s.Φinh.symm ((s.g (c, ωR)).1.items.eval ωR))]
     simp

theorem repair_right_collection_hippocratic {ΩL ΩR A B C D : Type u} {T : Type u → Type u}
  (s : LazyMutableCollectionSynchronizationBlock ΩL ΩR A B C D T) (a : A) (c : C) (ωL : ΩL) (ωR : ΩR)
  : consistent_collection s a c ωL ωR → (repair_right_collection s a c ωL ωR) = ωR
  := by
     simp
     intro h
     rw [h]
     exact (s.g (c, ωR)).1.apply_eval ωR

theorem repair_left_collection_hippocratic {ΩL ΩR A B C D : Type u} {T : Type u → Type u}
  (s : LazyMutableCollectionSynchronizationBlock ΩL ΩR A B C D T) (a : A) (c : C) (ωL : ΩL) (ωR : ΩR)
  : consistent_collection s a c ωL ωR → (repair_left_collection s a c ωL ωR) = ωL
  := by
     simp
     intro h
     have h_inv : s.Φinh.symm ((s.g (c, ωR)).1.items.eval ωR) = (s.f (a, ωL)).1.items.eval ωL
      := by
         symm
         rw [← h]
         simp
     rw [h_inv]
     exact (s.f (a, ωL)).1.apply_eval ωL

abbrev SetSynchronizationBlock (ΩL ΩR A B C D : Type u) := SynchronizationBlock ΩL ΩR A (Set B) C (Set D)

abbrev ListSynchronizationBlock (ΩL ΩR A B C D : Type u) := SynchronizationBlock ΩL ΩR A (List B) C (List D)

structure LazySetSemiSynchronizationBlock (ΩL ΩR A B C D : Type u) where
  f : Lens ΩL A (LazySet ΩL B)
  g : Lens ΩR C (LazySet ΩR D)
  Φbase : A ≃ C
  Φinh : B ≃ D
  f_persistent : persistent ΩL f
  g_persistent : persistent ΩR g
  f_putget : put_get ΩL f
  g_putget : put_get ΩR g

structure LazySetSynchronizationBlock (ΩL ΩR A B C D : Type u) extends LazySetSemiSynchronizationBlock ΩL ΩR A B C D where
  f_wellbehaved : well_behaved ΩL f
  g_wellbehaved : well_behaved ΩR g

structure LazyListSemiSynchronizationBlock (ΩL ΩR A B C D : Type u) where
  f : Lens ΩL A (LazyList ΩL B)
  g : Lens ΩR C (LazyList ΩR D)
  Φbase : A ≃ C
  Φinh : B ≃ D
  f_persistent : persistent ΩL f
  g_persistent : persistent ΩR g
  f_putget : put_get ΩL f
  g_putget : put_get ΩR g

structure LazyListSynchronizationBlock (ΩL ΩR A B C D : Type u) extends LazyListSemiSynchronizationBlock ΩL ΩR A B C D where
  f_wellbehaved : well_behaved ΩL f
  g_wellbehaved : well_behaved ΩR g

open LawfulBEq

@[simp]
def consistent_lazy_set {ΩL ΩR A B C D : Type u} (s : LazySetSemiSynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
  := Set.BijOn s.Φinh ((s.f.get (a,ωL)).1.eval ωL) ((s.g.get (c,ωR)).1.eval ωR)

@[simp]
def consistent_lazy_list {ΩL ΩR A B C D : Type u} [DecidableEq D] (s : LazyListSemiSynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
  := List.beq (((s.f.get (a,ωL)).1.eval ωL).map s.Φinh) ((s.g.get (c,ωR)).1.eval ωR)

@[simp]
def repair_right_lazy_list {ΩL ΩR A B C D : Type u} (s : LazyListSemiSynchronizationBlock ΩL ΩR A B C D) (a : A) (c : C) (ωL : ΩL) (ωR : ΩR)
  := (s.g.put ((c, lift_list_lazy (((s.f.get (a,ωL)).1.eval ωL).map s.Φinh)), ωR)).2

@[simp]
def repair_left_lazy_list {ΩL ΩR A B C D : Type u} (s : LazyListSemiSynchronizationBlock ΩL ΩR A B C D) (a : A) (c : C) (ωL : ΩL) (ωR : ΩR)
  := (s.f.put ((a, lift_list_lazy (((s.g.get (c,ωR)).1.eval ωR).map s.Φinh.symm)), ωL)).2

theorem left_repair_lazy_list_repairs_inconsistency {ΩL ΩR A B C D : Type u} [DecidableEq D] (s : LazyListSynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
  : consistent_lazy_list s.toLazyListSemiSynchronizationBlock (repair_left_lazy_list s.toLazyListSemiSynchronizationBlock a c ωL ωR) ωR a c
  := by
  simp
  have h_comega_cancels_out := s.f_persistent a (lift_list_lazy (((s.g.get (c, ωR)).1.eval ωR).map s.Φinh.invFun)) ωL
  simp at h_comega_cancels_out
  have h_simplifyput : (a, (s.f.put ((a, (lift_list_lazy (((s.g.get (c, ωR)).1.eval ωR).map s.Φinh.invFun))), ωL)).2) = (s.f.put ((a, (lift_list_lazy (((s.g.get (c, ωR)).1.eval ωR).map s.Φinh.invFun))), ωL)) :=
   by
   rw[Prod.mk_inj_right]
   symm
   exact h_comega_cancels_out
  simp at h_simplifyput
  rw[h_simplifyput]
  have f_getput := s.f_wellbehaved.right a ωL (lift_list_lazy (((s.g.get (c, ωR)).1.eval ωR).map s.Φinh.invFun))
  obtain ⟨c2, ht⟩ := f_getput
  obtain ⟨ω2,hc2⟩ := ht
  simp at hc2
  rw[hc2.left,hc2.right]
  simp
  induction ((s.g.get (c, ωR)).1.eval ωR) with
    | nil => rw[List.beq]
    | cons d ds hd => rw[List.beq,hd]; simp

lemma helper_because_list_beq_does_not_work {D : Type u} [DecidableEq D] (L1 L2 : List D)
  : L1.beq L2 = true → L1 = L2
  := by induction L1 generalizing L2 with
    | nil => intro h; cases L2 <;> first | rfl | contradiction
    | cons a as ih =>
      cases L2 with
      | nil => intro h; contradiction
      | cons b bs =>
        rw [List.beq]
        simp
        intro h1 h2
        simp at ih
        apply ih at h2
        exact And.intro h1 h2

abbrev eq_at_omega {A B C Ω : Type u} (m : morph Ω (C×(LazyList Ω A)) B) (ω : Ω)
  := ∀ c : C, ∀ l1 l2 : LazyList Ω A, l1.eval ω = l2.eval ω → m ((c,l1), ω) = m ((c,l2), ω)

lemma symm_inverts_list {A B : Type u} (l1 : List A) (l2 : List B) (eq : A ≃ B)
  : List.map eq l1 = l2 → List.map eq.symm l2 = l1
  := by
    intro h
    induction l1 generalizing l2 with
      | nil =>
        simp at h
        simp
        exact h
      | cons a as ha =>
        simp at h
        induction l2 with
          | nil => simp; contradiction
          | cons b bs =>
            simp
            rw [List.cons_eq_cons] at h
            have has := (ha bs) h.right
            have ha2 : eq.symm b = a
              := by
              rw [eq.symm_apply_eq]
              symm
              exact h.left
            exact And.intro ha2 has

theorem right_repair_lazy_list_hippocratic {ΩL ΩR A B C D : Type u} [DecidableEq D]
    (s : LazyListSynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
    (h : eq_at_omega s.g.put ωR)
  : consistent_lazy_list s.toLazyListSemiSynchronizationBlock ωL ωR a c → (repair_right_lazy_list s.toLazyListSemiSynchronizationBlock a c ωL ωR) = ωR
  := by
  simp
  intro hc
  have g_putget := s.g_wellbehaved.left (c,ωR)
  simp at g_putget
  rw[eq_at_omega] at h
  apply helper_because_list_beq_does_not_work (List.map (⇑s.Φinh) ((s.f.get (a, ωL)).1.eval ωL)) ((s.g.get (c, ωR)).1.eval ωR) at hc
  rw [hc]
  have h_put_ignores_omega := h c ({ eval := fun _ ↦ (s.g.get (c, ωR)).1.eval ωR }) (s.g.get (c, ωR)).1
  simp at h_put_ignores_omega
  rw [h_put_ignores_omega,g_putget]

theorem left_repair_lazy_list_hippocratic {ΩL ΩR A B C D : Type u} [DecidableEq D]
    (s : LazyListSynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
    (h : eq_at_omega s.f.put ωL)
  : consistent_lazy_list s.toLazyListSemiSynchronizationBlock ωL ωR a c → (repair_left_lazy_list s.toLazyListSemiSynchronizationBlock a c ωL ωR) = ωL
  := by
  simp
  intro hc
  have f_putget := s.f_wellbehaved.left (a,ωL)
  simp at f_putget
  rw[eq_at_omega] at h
  apply helper_because_list_beq_does_not_work (List.map (⇑s.Φinh) ((s.f.get (a, ωL)).1.eval ωL)) ((s.g.get (c, ωR)).1.eval ωR) at hc
  have hc2 : List.map (s.Φinh.symm) ((s.g.get (c, ωR)).1.eval ωR) = ((s.f.get (a, ωL)).1.eval ωL)
    := by
    apply symm_inverts_list
    exact hc
  rw [hc2]
  have h_put_ignores_omega := h a ({ eval := fun _ ↦ (s.f.get (a, ωL)).1.eval ωL }) (s.f.get (a, ωL)).1
  simp at h_put_ignores_omega
  rw [h_put_ignores_omega, f_putget]


/-
# Lifting
-/

@[simp]
def lift_equiv_list {A B : Type u} (Φ : A ≃ B) : (List A ≃ List B)
  := {
    toFun := List.map Φ,
    invFun := List.map Φ.invFun
    left_inv := List.map_leftInverse_iff.mpr Φ.left_inv
    right_inv := List.map_leftInverse_iff.mpr Φ.symm.left_inv
  }

@[simp]
def lift_equiv_multiset {A B : Type u} (Φ : A ≃ B) : (Multiset A ≃ Multiset B)
  := {
    toFun := Multiset.map Φ
    invFun := Multiset.map Φ.symm
    left_inv := by
      rw[Function.LeftInverse]
      intro a
      rw [Multiset.map_map]
      have h : Φ.symm ∘ Φ = Equiv.refl A
        := by simp
      rw[h]
      simp
    right_inv := by
      rw[Function.RightInverse]
      intro b
      simp
  }

@[simp]
def lift_equiv_set {A B : Type u} (Φ : A ≃ B) : (Finset A ≃ Finset B)
  := {
    toFun := Finset.map Φ
    invFun := Finset.map Φ.symm
    left_inv := by
      rw[Function.LeftInverse]
      intro a
      rw [Finset.map_map]
      have h : Φ.toEmbedding.trans Φ.symm.toEmbedding = Equiv.refl A
        := by simp
      rw[h]
      simp
    right_inv := by
      rw[Function.RightInverse]
      intro b
      rw[Finset.map_map]
      have h : Φ.symm.toEmbedding.trans Φ.toEmbedding = Equiv.refl B
        := by
        rw[← Equiv.symm_symm Φ]
        simp
      rw[h]
      simp
  }

@[simp]
def lift_equiv_orderedset {A B : Type u} [DecidableEq A] [DecidableEq B] (Φ : A ≃ B) : (OrderedSet A ≃ OrderedSet B)
  := {
    toFun := fun l => {
      items := (List.map Φ l.items).dedup
      nodup := by rw [← List.dedup_eq_self, List.dedup_idem]
    } ,
    invFun := fun l => {
      items := (List.map Φ.invFun l.items).dedup
      nodup := by rw [← List.dedup_eq_self, List.dedup_idem]
    }
    left_inv := by
      rw [Function.LeftInverse]
      intro a
      have h_aitems_dedup_eq : a.items.dedup = a.items
        := List.dedup_eq_self.mpr a.nodup
      have h_items : (List.map Φ.symm (List.map (Φ) a.items).dedup).dedup = a.items
        := by
           rw [List.dedup_map_of_injective Φ.injective]
           rw [h_aitems_dedup_eq]
           rw [List.map_map]
           simp
           exact h_aitems_dedup_eq
      simp_all
    right_inv := by
      rw [Function.RightInverse]
      intro b
      have h_bitems_dedup_eq : b.items.dedup = b.items
        := List.dedup_eq_self.mpr b.nodup
      have h_items : (List.map Φ (List.map (Φ.symm) b.items).dedup).dedup = b.items
        := by
           rw [List.dedup_map_of_injective Φ.symm.injective]
           rw [h_bitems_dedup_eq]
           rw [List.map_map]
           simp
           exact h_bitems_dedup_eq
      simp_all
  }

@[simp]
def unit_lazy_list_put { A B : Type u} (f : morph Ω (A×B) A) : morph Ω (A×(LazyList Ω B)) A
  := fun (a,ω) => let list := a.2.eval ω
     match list with
      | nil => (a.1, ω)
      | b :: _ => f ((a.1, b),ω)

@[simp]
def lift_morph_lazy_list {A B Ω : Type u} (l : Lens Ω A B) : Lens Ω A (LazyList Ω B)
 := {
  get := unit_lazy_list Ω l.get
  put := unit_lazy_list_put Ω l.put
  get_side_effect_free := by simp
 }

lemma lift_list_putget {A B Ω : Type u} (l : Lens Ω A B) : put_get Ω l → put_get Ω (lift_morph_lazy_list l) := by
  intro h
  simp
  intro a ω
  rw [put_get] at h
  exact h (a,ω)

lemma lift_list_persistent {A B Ω : Type u} (l : Lens Ω A B) : persistent Ω l → persistent Ω (lift_morph_lazy_list l) := by
  simp
  intro l_persistent
  intro a bs ω
  cases' bs.eval ω with b
  simp
  simp
  exact l_persistent a b ω

@[simp]
def lift_synchronizationBlock_lazy_list {ΩL ΩR A B C D : Type u} (b : SynchronizationBlock ΩL ΩR A B C D)
  : LazyListSemiSynchronizationBlock ΩL ΩR A B C D
  := {
    f := lift_morph_lazy_list b.f
    g := lift_morph_lazy_list b.g
    Φbase := b.Φbase
    Φinh := b.Φinh
    f_persistent := (lift_list_persistent b.f) b.f_persistent
    g_persistent := (lift_list_persistent b.g) b.g_persistent
    f_putget := (lift_list_putget b.f) b.f_wellbehaved.left
    g_putget := (lift_list_putget b.g) b.g_wellbehaved.left
  }

theorem lifted_synchronization_block_consistent_repair_right {ΩL ΩR A B C D : Type u}
   (s : SynchronizationBlock ΩL ΩR A B C D)
   (a : A) (c : C) (ωL : ΩL) (ωR : ΩR)
   : repair_right s a c ωL ωR = repair_right_lazy_list (lift_synchronizationBlock_lazy_list s) a c ωL ωR
   := by simp

theorem lifted_synchronization_block_consistent_repair_left {ΩL ΩR A B C D : Type u}
   (s : SynchronizationBlock ΩL ΩR A B C D)
   (a : A) (c : C) (ωL : ΩL) (ωR : ΩR)
   : repair_left s a c ωL ωR = repair_left_lazy_list (lift_synchronizationBlock_lazy_list s) a c ωL ωR
   := by simp

end MutableTypeCategories
