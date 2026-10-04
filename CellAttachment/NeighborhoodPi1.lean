module

public import CellAttachment.Deformation
public import CellAttachment.CoverPushout
public import CellAttachment.Annulus
public import CellAttachment.HomotopyPi1

@[expose] public section


/-! # The actual inclusion on pi1 factors through the proved neighborhood equivalence -/

noncomputable section
namespace CellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The neighborhood inclusion is an actual fundamental-group equivalence. -/
def neighborhoodPi1Equiv (f : ι → C(Circle, X)) (x₀ : X) :
    FundamentalGroup X x₀ ≃*
      FundamentalGroup (puncturedNeighborhood f) (neighborhoodInclusion f x₀) :=
  homotopyEquivPi1 (neighborhoodHomotopyEquiv f x₀) x₀

@[simp] theorem neighborhoodPi1Equiv_apply (f : ι → C(Circle, X)) (x₀ : X)
    (g : FundamentalGroup X x₀) :
    neighborhoodPi1Equiv f x₀ g = FundamentalGroup.map (neighborhoodInclusion f) x₀ g := rfl

/-- Factorization is through the actual inclusions, on every based loop class. -/
theorem inclusionPi1_factorization (f : ι → C(Circle, X)) (x₀ : X) :
    (FundamentalGroup.map (neighborhoodToSpace f) (neighborhoodInclusion f x₀)).comp
      (neighborhoodPi1Equiv f x₀).toMonoidHom = inclusionPi1 f x₀ := by
  ext g
  change Path.Homotopic.Quotient.map
    (Path.Homotopic.Quotient.map g (neighborhoodInclusion f)) (neighborhoodToSpace f) =
      Path.Homotopic.Quotient.map g (inclusion f)
  rw [← Path.Homotopic.Quotient.map_comp]
  rfl

/-- The required connectivity of the open neighborhood is proved from its
constructed homotopy equivalence; it is not an extra hypothesis. -/
theorem neighborhood_pathConnectedSpace (f : ι → C(Circle, X)) (x₀ : X)
    [PathConnectedSpace X] : PathConnectedSpace (puncturedNeighborhood f) :=
  homotopyEquivPathConnectedSpace (neighborhoodHomotopyEquiv f x₀).symm

/-- The deformation fixes every point of the original space at every time. -/
@[simp] theorem neighborhoodRadial_inclusion (f : ι → C(Circle, X)) (t : unitInterval) (x : X) :
    neighborhoodRadial f t (neighborhoodInclusion f x) = neighborhoodInclusion f x := by
  apply Subtype.ext
  rfl

/-- Retraction is invariant throughout the explicitly descended radial homotopy. -/
@[simp] theorem neighborhoodRetraction_radial (f : ι → C(Circle, X)) (x₀ : X)
    (t : unitInterval) (y : puncturedNeighborhood f) :
    neighborhoodRetraction f x₀ (neighborhoodRadial f t y) = neighborhoodRetraction f x₀ y := by
  obtain ⟨a,rfl⟩ := (puncturedQuotient_isQuotientMap f).surjective y
  rw [neighborhoodRadial_puncturedQuotient]
  change quotientRetraction f x₀ (puncturedQuotient f _) =
    quotientRetraction f x₀ (puncturedQuotient f a)
  rw [quotientRetraction_puncturedQuotient, quotientRetraction_puncturedQuotient]
  cases a with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i,z⟩
    change f i (polar (radialDeformation t z)) = f i (polar z)
    rw [polar_radialDeformation]

/-- The deformation trajectory projects to the constant path under retraction. -/
@[simp] theorem retraction_deformation_evalAt (f : ι → C(Circle, X)) (x₀ : X)
    (y : puncturedNeighborhood f) :
    ((neighborhoodDeformation f x₀).evalAt y).map (neighborhoodRetraction f x₀).continuous =
      Path.refl (neighborhoodRetraction f x₀ y) := by
  apply Path.ext
  funext t
  exact neighborhoodRetraction_radial f x₀ t y

/-- The inverse of the compatible neighborhood equivalence is the actual retraction map. -/
theorem neighborhoodPi1Equiv_symm_apply (f : ι → C(Circle, X)) (x₀ : X)
    (g : FundamentalGroup (puncturedNeighborhood f) (neighborhoodInclusion f x₀)) :
    (neighborhoodPi1Equiv f x₀).symm g =
      FundamentalGroup.map (neighborhoodRetraction f x₀) (neighborhoodInclusion f x₀) g := by
  obtain ⟨h,rfl⟩ := (neighborhoodPi1Equiv f x₀).surjective g
  rw [MulEquiv.symm_apply_apply, neighborhoodPi1Equiv_apply]
  change h = Path.Homotopic.Quotient.map
    (Path.Homotopic.Quotient.map h (neighborhoodInclusion f)) (neighborhoodRetraction f x₀)
  obtain ⟨p,rfl⟩ := Path.Homotopic.Quotient.mk_surjective h
  change Path.Homotopic.Quotient.mk p = Path.Homotopic.Quotient.mk
    ((p.map (neighborhoodInclusion f).continuous).map (neighborhoodRetraction f x₀).continuous)
  congr 1

end CellAttachment
