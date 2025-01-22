import NMF.MutableTypeCategories
import NMF.Collections
import NMF.SynchronizationBlocks

open MutableTypeCategories
open Finset
open Multiset
open Set
open List

variable (Ω : Type u)

namespace MutableTypeCategories


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
  f_getput : get_put ΩL f
  g_getput : get_put ΩR g

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


end MutableTypeCategories
