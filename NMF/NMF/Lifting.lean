import NMF.MutableTypeCategories

open MutableTypeCategories
open Finset
open Multiset
open Set
open List

variable (Ω : Type u)

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

lemma lift_list_getput {A B Ω : Type u} (l : Lens Ω A B) : get_put Ω l → get_put Ω (lift_morph_lazy_list l) := by
  intro h
  simp
  intro a ω
  rw [get_put] at h
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
    f_getput := (lift_list_getput b.f) b.f_wellbehaved.left
    g_getput := (lift_list_getput b.g) b.g_wellbehaved.left
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
