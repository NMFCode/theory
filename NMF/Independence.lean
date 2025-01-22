import NMF.MutableTypeCategories
import NMF.SynchronizationBlocks

open MutableTypeCategories

variable (Ω ΩL ΩR: Type v)

namespace MutableTypeCategories

def independent {A B C D : Type u} {Ω : Type v} (f : morph Ω A B) (g : morph Ω C D) : Prop
  := ∀ c : (C×Ω), ∀ a : A, (f (a, c.2)).1 = (f (a, (g c).2)).1

def mutual_independent {A B C D : Type u} (f : Lens Ω A B) (g : Lens Ω C D) : Prop
  := independent f.get g.put ∧ independent g.get f.put

lemma repair_right_mutual_independent_consistent {A1 A2 B1 B2 C1 C2 D1 D2}
  (s1 : SynchronizationBlock ΩL ΩR A1 B1 C1 D1) (s2 : SynchronizationBlock ΩL ΩR A2 B2 C2 D2)
  (a1 : A1) (a2 : A2) (c1 : C1) (c2 : C2) (ωL : ΩL) (ωR : ΩR) (h : independent s1.g.get s2.g.put)
  : let ωR1 := (repair_right s1 a1 c1 ωL ωR)
    let ωR2 := (repair_right s2 a2 c2 ωL ωR1)
    consistent s1 ωL ωR2 a1 c1
  := by
     simp
     have h_mutual := h ((c2, s2.Φinh (s2.f.get (a2, ωL)).1), (s1.g.put ((c1, s1.Φinh (s1.f.get (a1, ωL)).1), ωR)).2) c1
     rw [← h_mutual]
     have h_consistent_after2 := repair_right_repairs_inconsistency s1 ωL ωR a1 c1
     simp at h_consistent_after2
     rw [← h_consistent_after2]

lemma repair_right_chained_hippocratic {A1 A2 B1 B2 C1 C2 D1 D2}
  (s1 : SynchronizationBlock ΩL ΩR A1 B1 C1 D1) (s2 : SynchronizationBlock ΩL ΩR A2 B2 C2 D2)
  (a1 : A1) (a2 : A2) (c1 : C1) (c2 : C2) (ωL : ΩL) (ωR : ΩR)
  : consistent s1 ωL ωR a1 c1 ∧ consistent s2 ωL ωR a2 c2 →
    repair_right s2 a2 c2 ωL (repair_right s1 a1 c1 ωL ωR) = ωR
  := by
     intro h
     rw [repair_right_hippocratic s1 ωL ωR a1 c1 h.left, repair_right_hippocratic s2]
     exact h.right

lemma repair_left_mutual_independent_consistent {A1 A2 B1 B2 C1 C2 D1 D2}
  (s1 : SynchronizationBlock ΩL ΩR A1 B1 C1 D1) (s2 : SynchronizationBlock ΩL ΩR A2 B2 C2 D2)
  (a1 : A1) (a2 : A2) (c1 : C1) (c2 : C2) (ωL : ΩL) (ωR : ΩR) (h : independent s1.f.get s2.f.put)
  : let ωL1 := (repair_left s1 a1 c1 ωL ωR)
    let ωL2 := (repair_left s2 a2 c2 ωL1 ωR)
    consistent s1 ωL2 ωR a1 c1
  := by
     simp
     have h_mutual := h ((a2, s2.Φinh.symm (s2.g.get (c2, ωR)).1), (s1.f.put ((a1, s1.Φinh.symm (s1.g.get (c1, ωR)).1), ωL)).2) a1
     rw [← h_mutual]
     simp
     have h_consistent_after2 := repair_left_repairs_inconsistency s1 ωL ωR a1 c1
     simp at h_consistent_after2
     nth_rewrite 2 [← h_consistent_after2]
     rfl

lemma repair_left_chained_hippocratic {A1 A2 B1 B2 C1 C2 D1 D2}
  (s1 : SynchronizationBlock ΩL ΩR A1 B1 C1 D1) (s2 : SynchronizationBlock ΩL ΩR A2 B2 C2 D2)
  (a1 : A1) (a2 : A2) (c1 : C1) (c2 : C2) (ωL : ΩL) (ωR : ΩR)
  : consistent s1 ωL ωR a1 c1 ∧ consistent s2 ωL ωR a2 c2 →
    repair_left s2 a2 c2 (repair_left s1 a1 c1 ωL ωR) ωR = ωL
  := by
     intro h
     rw [repair_left_hippocratic s1 ωL ωR a1 c1 h.left, repair_left_hippocratic s2]
     exact h.right

end MutableTypeCategories
