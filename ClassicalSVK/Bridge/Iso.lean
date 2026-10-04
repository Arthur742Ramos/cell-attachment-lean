module

public import ClassicalSVK.Bridge.Naturality2

@[expose] public section


set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped FundamentalCategory

universe u

namespace ClassicalSVK

section
variable {X : Type u} [TopologicalSpace X]
local instance : Preorder X := universalPreorder X
local instance : DirectedSpace X := DirectedSpace.Preorder X
attribute [local instance] Path.Homotopic.setoid Dipath.Dihomotopic.setoid

lemma directedToClassical_comp_classicalToDirected :
    directedToClassical (X := X) ⋙ classicalToDirected (X := X) = 𝟭 (FundamentalCategory X) := by
  refine CategoryTheory.Functor.ext (fun x => rfl) ?_
  intro x y f
  simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact pathClassToDirectedClass_directedClassToPathClass f

lemma classicalToDirected_comp_directedToClassical :
    classicalToDirected (X := X) ⋙ directedToClassical (X := X) = 𝟭 (FundamentalGroupoid X) := by
  refine CategoryTheory.Functor.ext (fun x => rfl) ?_
  intro x y f
  simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact directedClassToPathClass_pathClassToDirectedClass f

end
end ClassicalSVK
