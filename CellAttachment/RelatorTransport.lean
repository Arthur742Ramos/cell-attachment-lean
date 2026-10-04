module

public import CellAttachment.NeighborhoodPi1
public import CellAttachment.CoverModels
public import CellAttachment.Statement

@[expose] public section


/-! # Actual radial paths identify the overlap generators with the attaching loops -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace CellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- Move from the original basepoint to an arbitrary neighborhood point along
an original-space path and the inverse of its genuine radial trajectory. -/
def radialAnchorPath (f : ι → C(Circle, X)) (x₀ : X) (y : puncturedNeighborhood f)
    (γ : Path x₀ (neighborhoodRetraction f x₀ y)) :
    Path (neighborhoodInclusion f x₀) y :=
  (γ.map (neighborhoodInclusion f).continuous).trans
    ((neighborhoodDeformation f x₀).evalAt y).symm

/-- Retraction of this chosen anchor path is the original path up to endpoint-fixed homotopy. -/
lemma radialAnchorPath_retraction_class (f : ι → C(Circle, X)) (x₀ : X)
    (y : puncturedNeighborhood f) (γ : Path x₀ (neighborhoodRetraction f x₀ y)) :
    Path.Homotopic.Quotient.mk
      ((radialAnchorPath f x₀ y γ).map (neighborhoodRetraction f x₀).continuous) =
      Path.Homotopic.Quotient.mk γ := by
  unfold radialAnchorPath
  rw [Path.map_trans, ← Path.map_symm, retraction_deformation_evalAt]
  have hg : (γ.map (neighborhoodInclusion f).continuous).map
      (neighborhoodRetraction f x₀).continuous = γ := by
    apply Path.ext
    funext t
    rfl
  rw [hg]
  simp [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_refl]

/-- The actual whiskered class at the neighborhood basepoint. -/
def radialWhiskerClass (f : ι → C(Circle, X)) (x₀ : X) (y : puncturedNeighborhood f)
    (γ : Path x₀ (neighborhoodRetraction f x₀ y)) (ℓ : Path y y) :
    FundamentalGroup (puncturedNeighborhood f) (neighborhoodInclusion f x₀) :=
  .mk ((radialAnchorPath f x₀ y γ).trans
    (ℓ.trans (radialAnchorPath f x₀ y γ).symm))

/-- Radial whiskering commutes with the actual retraction on based homotopy classes. -/
theorem retraction_radialWhiskerClass (f : ι → C(Circle, X)) (x₀ : X)
    (y : puncturedNeighborhood f) (γ : Path x₀ (neighborhoodRetraction f x₀ y))
    (ℓ : Path y y) :
    FundamentalGroup.map (neighborhoodRetraction f x₀) (neighborhoodInclusion f x₀)
      (radialWhiskerClass f x₀ y γ ℓ) =
      Path.Homotopic.Quotient.mk
        (γ.trans ((ℓ.map (neighborhoodRetraction f x₀).continuous).trans γ.symm)) := by
  change Path.Homotopic.Quotient.mk
    (((radialAnchorPath f x₀ y γ).trans
      (ℓ.trans (radialAnchorPath f x₀ y γ).symm)).map
        (neighborhoodRetraction f x₀).continuous) = _
  simp only [Path.map_trans, Path.Homotopic.Quotient.mk_trans, ← Path.map_symm,
    Path.Homotopic.Quotient.mk_symm, radialAnchorPath_retraction_class]

/-- The half-radius anchor viewed in the actual punctured neighborhood. -/
def attachmentAnchor (f : ι → C(Circle, X)) (i : ι) : puncturedNeighborhood f :=
  cellOverlapToNeighborhood f i (cellOverlapBasepoint f i)

@[simp] lemma retraction_attachmentAnchor (f : ι → C(Circle, X)) (x₀ : X) (i : ι) :
    neighborhoodRetraction f x₀ (attachmentAnchor f i) = f i 1 := by
  change neighborhoodRetraction f x₀
    (cellOverlapToNeighborhood f i (cellOverlapHomeomorph f i annulusBasepoint)) = _
  rw [neighborhoodRetraction_cellOverlap_coordinates, annulusPolar_basepoint]

/-- The actual original attaching whisker, with the radial anchor endpoint identified. -/
def chosenAttachmentAnchorPath (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) (i : ι) :
    Path (neighborhoodInclusion f x₀) (attachmentAnchor f i) :=
  radialAnchorPath f x₀ (attachmentAnchor f i)
    ((γ i).cast rfl (retraction_attachmentAnchor f x₀ i))

/-- The true half-circle loop viewed in the neighborhood. -/
def neighborhoodCellGenerator (f : ι → C(Circle, X)) (i : ι) :
    Path (attachmentAnchor f i) (attachmentAnchor f i) :=
  (cellOverlapGenerator f i).map (cellOverlapToNeighborhood f i).continuous

lemma retraction_neighborhoodCellGenerator (f : ι → C(Circle, X)) (x₀ : X) (i : ι) :
    (neighborhoodCellGenerator f i).map (neighborhoodRetraction f x₀).continuous =
      ((circleGenerator.map (f i).continuous).cast
        (retraction_attachmentAnchor f x₀ i) (retraction_attachmentAnchor f x₀ i)) := by
  apply Path.ext
  funext t
  change neighborhoodRetraction f x₀
    (cellOverlapToNeighborhood f i (cellOverlapHomeomorph f i (annulusGenerator t))) =
      f i (circleGenerator t)
  rw [neighborhoodRetraction_cellOverlap_coordinates]
  exact congrArg (f i) (annulusPolar_halfCircle (circleGenerator t))

/-- The neighborhood relator obtained from the actual radial choice of paths. -/
def chosenNeighborhoodRelator (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) (i : ι) :
    FundamentalGroup (puncturedNeighborhood f) (neighborhoodInclusion f x₀) :=
  .mk ((chosenAttachmentAnchorPath f x₀ γ i).trans
    ((neighborhoodCellGenerator f i).trans (chosenAttachmentAnchorPath f x₀ γ i).symm))

/-- Retraction sends the genuine overlap relator to precisely the requested attaching loop. -/
theorem retraction_chosenNeighborhoodRelator (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) (i : ι) :
    FundamentalGroup.map (neighborhoodRetraction f x₀) (neighborhoodInclusion f x₀)
      (chosenNeighborhoodRelator f x₀ γ i) = attachingLoopClass f x₀ γ i := by
  change FundamentalGroup.map (neighborhoodRetraction f x₀) (neighborhoodInclusion f x₀)
    (radialWhiskerClass f x₀ (attachmentAnchor f i)
      ((γ i).cast rfl (retraction_attachmentAnchor f x₀ i)) (neighborhoodCellGenerator f i)) = _
  rw [retraction_radialWhiskerClass, retraction_neighborhoodCellGenerator]
  change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk (attachingLoop f x₀ γ i)
  congr 1

/-- The compatible neighborhood equivalence sends every attaching relator to the actual
transported half-circle relator. -/
theorem neighborhoodPi1Equiv_attachingLoopClass (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) (i : ι) :
    neighborhoodPi1Equiv f x₀ (attachingLoopClass f x₀ γ i) =
      chosenNeighborhoodRelator f x₀ γ i := by
  apply (neighborhoodPi1Equiv f x₀).symm.injective
  rw [MulEquiv.symm_apply_apply, neighborhoodPi1Equiv_symm_apply,
    retraction_chosenNeighborhoodRelator]

end CellAttachment
