import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Limits.Cones

open CategoryTheory

namespace MutableTypeCategories

universe v u

variable (Ω : Type u)

structure MutableMorphism (A B : Type u) where
  eval : (A × Ω) → (B × Ω)

@[simp]
abbrev morph (A B : Type u) : Type u := (A×Ω) → (B×Ω)

@[simp]
abbrev comp {A B C : Type u} (f : morph Ω A B) (g : morph Ω B C) : morph Ω A C
  := fun a => g (f a)

@[simp]
def side_effect_free {A B Ω : Type u} (f : morph Ω A B) : Prop
 := ∀ a : A × Ω, (f a).snd = a.snd

@[simp]
def stateless {A B Ω : Type u} (f : morph Ω A B) : Prop
 := ∀ a : A, ∀ ω : Ω, ∀ ω2 : Ω, (f (a,ω)).1 = (f (a,ω2)).1

@[simp]
def id_morph (A : Type u) : morph Ω A A
 := @id (A × Ω)

lemma id_sef (A : Type u) : side_effect_free (id_morph Ω A) := by
  rw [side_effect_free]
  rw [id_morph]
  simp

lemma comp_side_effect_free {A B C Ω : Type u} (f : morph Ω A B) (g : morph Ω B C)
  : side_effect_free f ∧ side_effect_free g → side_effect_free (comp Ω f g) := by
  intro H
  rw[side_effect_free]
  intro a
  rw[comp]
  rw [H.right, H.left]

instance MutableTypeCategory : Category.{u} (Type u) where
  Hom A B := morph Ω A B
  id A := id_morph Ω A
  comp f g := fun a => g ( f a )

structure Lens (Ω A B : Type u) where
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
    get := fun a => g.get (f.get a)
    put := fun a =>
      let gput := g.put (((f.get (a.fst.fst, a.snd)).fst, a.fst.snd), a.snd)
      f.put ((a.fst.fst, gput.fst), gput.snd)
    get_side_effect_free := by
      rw [side_effect_free]
      intro a
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

end MutableTypeCategories
