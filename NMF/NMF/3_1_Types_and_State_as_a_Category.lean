import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Limits.Cones

open CategoryTheory
#print Limits.Cone

-- Definition 19 (Side-effect free methods)
def side_effect_free {A B Ω : Type u} (f : A × Ω → B × Ω) := ∀ x : A × Ω, (f x).2 = x.2

#check id

#check (Type 0 → Type 0 : Type 1)


-- Example 17
example {A Ω: Type u}: side_effect_free (@id (A×Ω)) := by simp [side_effect_free]

-- Proposition 4
-- A composition of side-effect free morphisms is side-effect free.
-- TODO Wie ist hier Morphismus und side-effect free definiert?

-- Definition 20 (Mutable Type Category)
variable (obT : Set (Type u))
variable (Ω : Type u)
def obC := {A : Type u // A ∈ obT} × {Ω' : Type u // Ω' = Ω}
-- variable (X : obC obT Ω)
-- #check X.1.val
-- #check obC obT
-- def Mor_obC (X Y : obC obT Ω) := X.1.val × X.2.val→ Y.1.val × Y.2.val
-- #check Mor_obC

instance MutableTypeCategory :
  Category (obC obT Ω) where
  -- X ⟶ Y (X "quiver" Y)
  Hom X Y := X.1.val × Ω → Y.1.val × Ω
  -- 𝟙
  id X := fun X => X
  -- f ≫ g
  comp f g := fun X => (g (f X))

lemma id_side_effect_free {A Ω : Type u}:
  side_effect_free (fun x : A × Ω => x) := by simp[side_effect_free]
lemma comp_side_effect_free' {A B C Ω : Type u}
  {f : A × Ω → B × Ω} {g : B × Ω → C × Ω}
  {h1 : side_effect_free f} {h2 : side_effect_free g}:
  side_effect_free (fun x => g (f x)) := by
    unfold side_effect_free at *
    intros x
    dsimp
    rw [h2, h1]

def MTC_comp {X Y Z : obC obT Ω}
  (f : X.1.val × Ω → Y.1.val × Ω)
  (g : Y.1.val × Ω → Z.1.val × Ω) :=
  fun x : X.1.val × Ω => g (f x)

lemma comp_side_effect_free {X Y Z : obC obT Ω}
  {f : X.1.val × Ω → Y.1.val × Ω}
  {g : Y.1.val × Ω → Z.1.val × Ω}
  (h1 : side_effect_free f) (h2 : side_effect_free g):
  side_effect_free (MTC_comp obT Ω f g) := by
    unfold MTC_comp
    apply comp_side_effect_free'
    apply h1
    apply h2

instance MutableTypeCategory_Ω :
  Category (obC obT Ω) where
  -- X ⟶ Y (X "quiver" Y)
  Hom X Y := {f : X.1.val × Ω → Y.1.val × Ω // side_effect_free f}
  -- 𝟙
  id X := Subtype.mk (fun (x : X.1.val × Ω) => x) id_side_effect_free
  -- f ≫ g
  comp :=
    fun {X Y Z} (f : {f : X.1.val × Ω → Y.1.val × Ω // side_effect_free f})
                (g : {g : Y.1.val × Ω → Z.1.val × Ω // side_effect_free g}) =>
    Subtype.mk
      (MTC_comp obT Ω f g)
      (comp_side_effect_free obT Ω f.property g.property)

-- TODO We further demand that the restriction of C to side-effect free
--      morphisms C_Ω forms a cartesian-closed category.

#check MutableTypeCategory


-- class ClosedTypeSet (A : Type u) where
--   prod: ∀ (X : {X : Type u // })

def c := MutableTypeCategory obT Ω
def c1 := MutableTypeCategory_Ω obT Ω

-- universe v u
-- typeclass Category (obj : Type u) where
-- -- Quiver
--   Hom : obj → obj → Type v
-- -- CategoryStruct
--   -- (X : obj) → (V : Type v): V := Hom X X
--   id : ∀ X : obj, Hom X X -- 𝟙
--   -- {X Y Z : obj} → (f : Hom X Y) → (g : Hom Y Z) → (V : Hom X Z)
--   -- f ≫ g = g ∘ f
--   comp : {X Y Z : obj} →  (Hom X Y) → (Hom Y Z) → (Hom X Z)
-- -- Category
--   id_comp : ∀ {X Y : obj} (f : X ⟶ Y), id X ≫ f = f := by aesop_cat
