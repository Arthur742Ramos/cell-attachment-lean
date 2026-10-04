module

public import Lean4.constructions
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Elementwise

@[expose] public section


/-!
Bundled category of directed spaces. This follows the current Mathlib
`TopCat` structure instead of the removed `BundledHom` API.
-/

open DirectedMap
open CategoryTheory

universe u

structure dTopCat where
  /-- Underlying type. -/
  carrier : Type u
  /-- Topology and directed structure on the underlying type. -/
  [str : DirectedSpace carrier]

attribute [instance] dTopCat.str

namespace dTopCat

instance : CoeSort dTopCat (Type u) := ⟨dTopCat.carrier⟩

instance : Category dTopCat where
  Hom X Y := DirectedMap X Y
  id X := DirectedMap.id X
  comp f g := DirectedMap.comp g f
  id_comp f := DirectedMap.comp_id f
  comp_id f := DirectedMap.id_comp f
  assoc f g h := (DirectedMap.comp_assoc h g f).symm

instance concreteCategory : ConcreteCategory dTopCat (fun X Y => DirectedMap X Y) where
  hom f := f
  ofHom f := f

instance directedSpaceUnbundled (X : dTopCat) : DirectedSpace X := X.str

instance (X Y : dTopCat) : CoeFun (X ⟶ Y) (fun _ => X → Y) where
  coe f := f

lemma id_app (X : dTopCat.{u}) (x : ↑X) : (𝟙 X : X → X) x = x := rfl

lemma comp_app {X Y Z : dTopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g : X → Z) x = g (f x) := rfl

/-- Construct a bundled directed space. -/
def of (X : Type u) [DirectedSpace X] : dTopCat := ⟨X⟩

instance directedSpace_coe (X : dTopCat) : DirectedSpace X := X.str

@[reducible]
instance directedSpace_forget (X : dTopCat) : DirectedSpace <| (forget dTopCat).obj X := X.str

instance subspace_coe {X : dTopCat} : CoeTC (Set X) dTopCat := ⟨fun s => dTopCat.of s⟩

def DirectedSubtypeHom {X : dTopCat} (Y : Set X) : (dTopCat.of Y) ⟶ X :=
  DirectedSubtypeInclusion (fun s => s ∈ Y)

def DirectedSubsetHom {X : dTopCat} {Y₀ Y₁ : Set X} (h : Y₀ ⊆ Y₁) : (dTopCat.of Y₀) ⟶ Y₁ :=
  DirectedSubsetInclusion h

end dTopCat
