import NMF.MutableTypeCategories
import NMF.Lenses

open CategoryTheory

universe u v

variable (Ω : Type v)

namespace MutableTypeCategories


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

theorem repair_right_repairs_inconsistency {ΩL ΩR A B C D : Type u} (s : SynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
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

theorem repair_left_repairs_inconsistency {ΩL ΩR A B C D : Type u} (s : SynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
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

theorem repair_right_hippocratic {ΩL ΩR A B C D : Type u} (s : SynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
  : consistent s ωL ωR a c → (repair_right s a c ωL ωR) = ωR
  := by
  simp
  intro hc
  rw[hc]
  have g_putget := s.g_wellbehaved.left (c,ωR)
  simp at g_putget
  rw[g_putget]

theorem repair_left_hippocratic {ΩL ΩR A B C D : Type u} (s : SynchronizationBlock ΩL ΩR A B C D) (ωL : ΩL) (ωR : ΩR) (a : A) (c : C)
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
