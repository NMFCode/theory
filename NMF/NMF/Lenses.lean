import NMF.MutableTypeCategories

open CategoryTheory

universe u v

variable (Ω : Type v)

namespace MutableTypeCategories

/-
# Synchronization block theory and lenses
-/

structure Lens (Ω : Type v) (A B : Type u) where
  get : morph Ω A B
  put : morph Ω (A × B) A
  get_side_effect_free : side_effect_free get

@[simp]
def get_put (f : Lens Ω A B) :=
  ∀ a : A×Ω, f.put ((a.fst, (f.get a).fst), a.snd) = a

@[simp]
def put_get (f : Lens Ω A B) :=
  ∀ a : A, ∀ ω : Ω, ∀ b : B, ∃ a2 : A, ∃ ω2 : Ω, f.put ((a,b), ω) = (a2,ω2) ∧ f.get (a2, ω2) = (b,ω2)

@[simp]
def well_behaved (f : Lens Ω A B) := get_put Ω f ∧ put_get Ω f

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

theorem comp_wellbehaved_getput { A B C : Type u} (f : Lens Ω A B) (g : Lens Ω B C) :
  well_behaved Ω f ∧ well_behaved Ω g → get_put Ω (Lens.comp Ω f g) := by
  intro H
  have f_wellbehaved : well_behaved Ω f := H.left
  have g_wellbehaved : well_behaved Ω g := H.right
  rw [get_put]
  intro a
  rw [Lens.comp]
  simp
  have g_getput := g_wellbehaved.left (f.get a)
  have hSimpleF : (f.get a).2 = a.2 := by
    rw[f.get_side_effect_free]
  rw[hSimpleF] at g_getput
  rw[g_getput]
  have f_getput := f_wellbehaved.left a
  rw [← hSimpleF] at f_getput
  exact f_getput

theorem comp_transient_wellbehaved { A B C : Type u} (f : Lens Ω A B) (g : Lens Ω B C) :
  well_behaved Ω f ∧ well_behaved Ω g ∧ stateless g.get → well_behaved Ω (Lens.comp Ω f g) := by
  intro H
  have f_wellbehaved : well_behaved Ω f := H.left
  have g_wellbehaved : well_behaved Ω g := H.right.left
  have g_stateless := H.right.right
  apply And.intro
  exact comp_wellbehaved_getput Ω f g (And.intro f_wellbehaved g_wellbehaved)
  rw [put_get]
  intro a ω c
  rw [Lens.comp]
  simp
  have f_putget := f_wellbehaved.right a (g.put (((f.get (a, ω)).1, c), ω)).2 (g.put (((f.get (a, ω)).1, c), ω)).1
  obtain ⟨a2,ht⟩ := f_putget
  obtain ⟨ω2,ha2⟩ := ht
  rw[ha2.left]
  use a2
  use ω2
  apply And.intro
  rfl
  have ha3 := ha2.right
  rw[ha3]
  have g_putget := g_wellbehaved.right (f.get (a,ω)).1 ω c
  obtain ⟨b, ht⟩ := g_putget
  obtain ⟨ω3, ht2⟩ := ht
  have g_getput := ht2.right
  rw[← ht2.left] at g_getput
  have c_equals := g_stateless (g.put (((f.get (a, ω)).1, c), ω)).1 (g.put (((f.get (a, ω)).1, c), ω)).2 ω2
  rw [g_getput] at c_equals
  simp at c_equals
  have omega_keeps : (g.get ((g.put (((f.get (a, ω)).1, c), ω)).1, ω2)).2 = ω2
    := g.get_side_effect_free ((g.put (((f.get (a, ω)).1, c), ω)).1, ω2)
  nth_rewrite 2 [c_equals]
  nth_rewrite 3 [← omega_keeps]
  simp

end MutableTypeCategories
