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

end MutableTypeCategories
