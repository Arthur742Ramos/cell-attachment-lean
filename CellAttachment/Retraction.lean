module

public import CellAttachment.RawNeighborhood

@[expose] public section


/-!
# Radial retraction onto the original space

The descent below uses the actual quotient map on the open punctured neighborhood.
No retraction is assumed as a hypothesis.
-/

noncomputable section
namespace CellAttachment
universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

@[simp] lemma polar_boundary (z : Circle) :
    polar ⟨boundaryInclusion z, Circle.coe_ne_zero z⟩ = z := by
  apply Circle.ext
  change (‖(z : ℂ)‖⁻¹ : ℝ) • (z : ℂ) = z
  simp

/-- An algebraic extension to disk centers, used only to define quotient descent.
Continuity is asserted only after restricting to the punctured neighborhood. -/
def rawRetraction (f : ι → C(Circle, X)) (x₀ : X) : Raw X ι → X
  | .inl x => x
  | .inr ⟨i,z⟩ => if h : (z : ℂ) ≠ 0 then f i (polar ⟨z,h⟩) else x₀

lemma rawRetraction_respects (f : ι → C(Circle, X)) (x₀ : X)
    {a b : Raw X ι} (h : AttachingRel f a b) : rawRetraction f x₀ a = rawRetraction f x₀ b := by
  cases h with
  | boundary i z =>
    change (if h : (z : ℂ) ≠ 0 then f i (polar ⟨boundaryInclusion z,h⟩) else x₀) = f i z
    rw [dite_eq_left (Circle.coe_ne_zero z), polar_boundary]

/-- Algebraic quotient descent, prior to its restriction to the continuous domain. -/
def quotientRetraction (f : ι → C(Circle, X)) (x₀ : X) : Space f → X :=
  Quot.lift (rawRetraction f x₀) (fun _ _ h => rawRetraction_respects f x₀ h)

@[simp] lemma quotientRetraction_inclusion (f : ι → C(Circle, X)) (x₀ x : X) :
    quotientRetraction f x₀ (inclusion f x) = x := rfl

/-- On the punctured raw coproduct the retraction is continuous componentwise. -/
lemma quotientRetraction_puncturedQuotient (f : ι → C(Circle, X)) (x₀ : X)
    (a : PuncturedRaw X ι) :
    quotientRetraction f x₀ (puncturedQuotient f a) =
      Sum.elim id (fun z : Σ _ : ι, PuncturedDisk => f z.1 (polar z.2)) a := by
  cases a with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i,z⟩
    exact dite_eq_left z.property

lemma quotientRetraction_continuousOnNeighborhood (f : ι → C(Circle, X)) (x₀ : X) :
    Continuous (fun y : puncturedNeighborhood f => quotientRetraction f x₀ y) := by
  apply (puncturedQuotient_isQuotientMap f).continuous_iff.mpr
  have h : Continuous (Sum.elim id
      (fun z : Σ _ : ι, PuncturedDisk => f z.1 (polar z.2))) := by
    apply Continuous.sumElim continuous_id
    apply continuous_sigma
    intro i
    exact (f i).continuous.comp polar.continuous
  simpa only [Function.comp_def, quotientRetraction_puncturedQuotient] using h

/-- The proved continuous retraction onto the actual original space. -/
def neighborhoodRetraction (f : ι → C(Circle, X)) (x₀ : X) :
    C(puncturedNeighborhood f, X) :=
  ⟨fun y => quotientRetraction f x₀ y, quotientRetraction_continuousOnNeighborhood f x₀⟩

/-- The actual inclusion, codomain-restricted to the punctured neighborhood. -/
def neighborhoodInclusion (f : ι → C(Circle, X)) : C(X, puncturedNeighborhood f) :=
  ⟨fun x => ⟨inclusion f x, inclusion_not_mem_centers f x⟩,
    (inclusion f).continuous.subtype_mk _⟩

@[simp] theorem neighborhoodRetraction_inclusion (f : ι → C(Circle, X)) (x₀ x : X) :
    neighborhoodRetraction f x₀ (neighborhoodInclusion f x) = x := rfl

end CellAttachment
