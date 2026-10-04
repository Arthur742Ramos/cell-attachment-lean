module

public import ClassicalSVK.Bridge.Naturality

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

lemma classicalToDirected_naturality (f : dTopCat.of X ⟶ dTopCat.of Y) :
    (CategoryTheory.Grpd.forgetToCat.map
        (FundamentalGroupoid.fundamentalGroupoidFunctor.map
          (TopCat.ofHom f.toContinuousMap))).toFunctor ⋙
      classicalToDirected (X := Y) =
      classicalToDirected (X := X) ⋙
        (FundamentalCategory.fundamentalCategoryFunctor.map f).toFunctor := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro x y q
  change pathClassToDirectedClass (q.map f.toContinuousMap) ≍
    Dipath.Dihomotopic.Quotient.mapFn (pathClassToDirectedClass q) f
  refine Quotient.inductionOn q ?_
  intro p
  change (⟦pathToDipath (p.map f.toContinuousMap.continuous)⟧ : Dipath.Dihomotopic.Quotient _ _) ≍
    ⟦(pathToDipath p).map f⟧
  have hp : pathToDipath (p.map f.toContinuousMap.continuous) = (pathToDipath p).map f := by
    apply Dipath.ext
    funext t
    rfl
  rw [hp]
  rfl

end
end ClassicalSVK
