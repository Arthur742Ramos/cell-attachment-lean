module

public import Lean4.dTop
public import Lean4.dihomotopy_to_path_dihomotopy
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section


open CategoryTheory
open scoped unitInterval FundamentalCategory

attribute [local instance_reducible] DirectedSpace.Preorder

universe u

namespace ClassicalSVK

@[instance_reducible]
def universalPreorder (X : Type u) : Preorder X where
  le := fun _ _ => True
  le_refl := by intro x; trivial
  le_trans := by intro x y z hxy hyz; trivial

section
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
local instance : Preorder X := universalPreorder X
local instance : Preorder Y := universalPreorder Y
local instance : DirectedSpace X := DirectedSpace.Preorder X
local instance : DirectedSpace Y := DirectedSpace.Preorder Y
attribute [local instance] Path.Homotopic.setoid Dipath.Dihomotopic.setoid

noncomputable def pathToDipath {x y : X} (p : Path x y) : Dipath x y :=
  Dipath.of_isDipath (γ := p) (by intro a b hab; trivial)

theorem pathToDipath_toPath {x y : X} (p : Path x y) : (pathToDipath p).toPath = p := rfl

theorem dipathDihomotopic_to_pathHomotopic {x y : X} {p q : Dipath x y}
    (h : p.Dihomotopic q) : p.toPath.Homotopic q.toPath := by
  refine Relation.EqvGen.rec
    (motive := fun p q _ => p.toPath.Homotopic q.toPath)
    ?_ ?_ ?_ ?_ h
  · intro p q h
    rcases h with ⟨H⟩
    exact ⟨H.dihom_to_hom⟩
  · intro p
    exact Path.Homotopic.refl _
  · intro p q h hpq
    exact Path.Homotopic.symm hpq
  · intro p q r hpq hqr hpq' hqr'
    exact Path.Homotopic.trans hpq' hqr'

theorem pathHomotopic_to_dipathDihomotopic {x y : X} {p q : Path x y}
    (h : p.Homotopic q) : (pathToDipath p).Dihomotopic (pathToDipath q) := by
  rcases h with ⟨H⟩
  exact Relation.EqvGen.rel _ _ ⟨Dipath.Dihomotopy.hom_to_dihom
    (p₀ := pathToDipath p) (p₁ := pathToDipath q) H
    (by intro a b γ hγ; change Monotone _; intro s t hst; trivial)⟩

noncomputable def directedClassToPathClass {x y : X}
    (f : Dipath.Dihomotopic.Quotient x y) : Path.Homotopic.Quotient x y :=
  Quotient.liftOn f (fun p => (⟦p.toPath⟧ : Path.Homotopic.Quotient x y))
    (fun p q hpq => Quotient.sound (dipathDihomotopic_to_pathHomotopic hpq))

noncomputable def pathClassToDirectedClass {x y : X}
    (f : Path.Homotopic.Quotient x y) : Dipath.Dihomotopic.Quotient x y :=
  Quotient.liftOn f (fun p => (⟦pathToDipath p⟧ : Dipath.Dihomotopic.Quotient x y))
    (fun p q hpq => Quotient.sound (pathHomotopic_to_dipathDihomotopic hpq))

lemma pathClassToDirectedClass_directedClassToPathClass {x y : X}
    (f : Dipath.Dihomotopic.Quotient x y) :
    pathClassToDirectedClass (directedClassToPathClass f) = f := by
  refine Quotient.inductionOn f ?_
  intro p
  change (⟦pathToDipath p.toPath⟧ : Dipath.Dihomotopic.Quotient x y) = ⟦p⟧
  have hp : pathToDipath p.toPath = p := by
    apply Dipath.ext
    funext t
    rfl
  rw [hp]

lemma directedClassToPathClass_pathClassToDirectedClass {x y : X}
    (f : Path.Homotopic.Quotient x y) :
    directedClassToPathClass (pathClassToDirectedClass f) = f := by
  refine Quotient.inductionOn f ?_
  intro p
  change (⟦(pathToDipath p).toPath⟧ : Path.Homotopic.Quotient x y) = ⟦p⟧
  rfl

noncomputable def directedToClassical : FundamentalCategory X ⥤ FundamentalGroupoid X where
  obj x := ⟨x.as⟩
  map f := directedClassToPathClass f
  map_id x := by
    change (⟦(Dipath.refl x.as).toPath⟧ : Path.Homotopic.Quotient x.as x.as) = ⟦Path.refl x.as⟧
    rfl
  map_comp := by
    intro x y z f g
    rw [FundamentalCategory.comp_eq, FundamentalGroupoid.comp_eq]
    refine Quotient.inductionOn₂ f g ?_
    intro p q
    rfl

noncomputable def classicalToDirected : FundamentalGroupoid X ⥤ FundamentalCategory X where
  obj x := ⟨x.as⟩
  map f := pathClassToDirectedClass f
  map_id x := by
    change (⟦pathToDipath (Path.refl x.as)⟧ : Dipath.Dihomotopic.Quotient x.as x.as) = ⟦Dipath.refl x.as⟧
    have hp : pathToDipath (Path.refl x.as) = Dipath.refl x.as := by
      apply Dipath.ext
      funext t
      rfl
    rw [hp]
  map_comp := by
    intro x y z f g
    rw [FundamentalGroupoid.comp_eq, FundamentalCategory.comp_eq]
    refine Quotient.inductionOn₂ f g ?_
    intro p q
    change (⟦pathToDipath (p.trans q)⟧ : Dipath.Dihomotopic.Quotient x.as z.as) =
      ⟦(pathToDipath p).trans (pathToDipath q)⟧
    have hp : pathToDipath (p.trans q) = (pathToDipath p).trans (pathToDipath q) := by
      apply Dipath.ext
      funext t
      rfl
    rw [hp]

end
end ClassicalSVK
