module

public import ClassicalSVK.Bridge.Categories

@[expose] public section


open CategoryTheory
open scoped unitInterval FundamentalCategory

universe u

namespace ClassicalSVK

section
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
local instance : Preorder X := universalPreorder X
local instance : Preorder Y := universalPreorder Y
local instance : DirectedSpace X := DirectedSpace.Preorder X
local instance : DirectedSpace Y := DirectedSpace.Preorder Y
attribute [local instance] Path.Homotopic.setoid Dipath.Dihomotopic.setoid

lemma directedToClassical_naturality (f : dTopCat.of X ⟶ dTopCat.of Y) :
    (FundamentalCategory.fundamentalCategoryFunctor.map f).toFunctor ⋙
        directedToClassical (X := Y) =
        directedToClassical (X := X) ⋙
        (CategoryTheory.Grpd.forgetToCat.map
          (FundamentalGroupoid.fundamentalGroupoidFunctor.map
            (TopCat.ofHom f.toContinuousMap))).toFunctor := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro x y q
  change directedClassToPathClass (Dipath.Dihomotopic.Quotient.mapFn q f) ≍
    (directedClassToPathClass q).map f.toContinuousMap
  refine Quotient.inductionOn q ?_
  intro p
  rfl

end
end ClassicalSVK
