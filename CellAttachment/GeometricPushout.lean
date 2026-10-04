module

public import CellAttachment.GroupoidQuotient
public import CellAttachment.CoverModels
public import CellAttachment.NeighborhoodPi1

@[expose] public section


/-!
# Vertex groups of the genuine cell-attachment open cover

This file applies the categorical quotient bridge to the actual fundamental
groupoids of the established open cover. The relators are the actual half-circle
classes in the overlap, transported by an arbitrary specified family of paths.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace CellAttachment

universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The actual half-radius anchor of cell `i`, regarded as a point of the full overlap. -/
def coverOverlapAnchor (f : ι → C(Circle, X)) (i : ι) : overlap f :=
  cellOverlapToOverlap f i (cellOverlapBasepoint f i)

/-- The actual half-circle generator class, included in the full overlap. -/
def coverOverlapGeneratorClass (f : ι → C(Circle, X)) (i : ι) :
    FundamentalGroup (overlap f) (coverOverlapAnchor f i) :=
  FundamentalGroup.map (cellOverlapToOverlap f i) (cellOverlapBasepoint f i)
    (cellOverlapGeneratorClass f i)

@[simp] theorem coverOverlapAnchor_eq (f : ι → C(Circle, X)) (i : ι) :
    coverOverlapAnchor f i = overlapAnchor f i := rfl

@[simp] theorem coverOverlapGeneratorClass_eq (f : ι → C(Circle, X)) (i : ι) :
    coverOverlapGeneratorClass f i = overlapAnchorGeneratorClass f i := rfl

/-- The relator in the actual punctured-neighborhood vertex group, transported
using the specified path from the original basepoint to that cell's overlap anchor. -/
def neighborhoodTransportedRelator (f : ι → C(Circle, X)) (x₀ : X)
    (p : ∀ i : ι, Path (neighborhoodInclusion f x₀)
      (overlapLeft f (coverOverlapAnchor f i))) (i : ι) :
    FundamentalGroup (puncturedNeighborhood f) (neighborhoodInclusion f x₀) :=
  overlapLoop (FundamentalGroupoid.map (overlapLeft f))
    (FundamentalGroupoid.mk (neighborhoodInclusion f x₀))
    (FundamentalGroupoid.mk (coverOverlapAnchor f i))
    (Path.Homotopic.Quotient.mk (p i)) (coverOverlapGeneratorClass f i)

/-- The transported relator is the genuine whiskered half-circle path class. -/
theorem neighborhoodTransportedRelator_path (f : ι → C(Circle, X)) (x₀ : X)
    (p : ∀ i : ι, Path (neighborhoodInclusion f x₀)
      (overlapLeft f (coverOverlapAnchor f i))) (i : ι) :
    neighborhoodTransportedRelator f x₀ p i = Path.Homotopic.Quotient.mk
      ((p i).trans (((cellOverlapGenerator f i).map
        (cellOverlapToNeighborhood f i).continuous).trans (p i).symm)) := by
  change Path.Homotopic.Quotient.mk (p i) ≫
    (FundamentalGroupoid.map (overlapLeft f)).map (coverOverlapGeneratorClass f i) ≫
      inv (Path.Homotopic.Quotient.mk (p i)) = _
  rw [← Groupoid.inv_eq_inv]
  change (Path.Homotopic.Quotient.mk (p i)).trans
    (((Path.Homotopic.Quotient.mk (cellOverlapGenerator f i)).map
      (cellOverlapToOverlap f i)).map (overlapLeft f) |>.trans
        (Path.Homotopic.Quotient.mk (p i).symm)) = _
  rw [← Path.Homotopic.Quotient.map_comp]
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_trans]

/-- The overlap inclusion is injective on the actual groupoid objects. -/
theorem overlapLeft_groupoid_obj_injective (f : ι → C(Circle, X)) :
    Function.Injective (FundamentalGroupoid.map (overlapLeft f)).obj := by
  rintro ⟨a⟩ ⟨b⟩ h
  congr 1
  apply Subtype.ext
  exact congrArg (fun z => z.as.1) h

/-- The original basepoint lies outside the actual overlap object image. -/
theorem neighborhood_base_outside_overlap (f : ι → C(Circle, X)) (x₀ : X)
    (w : FundamentalGroupoid (overlap f)) :
    (FundamentalGroupoid.map (overlapLeft f)).obj w ≠
      FundamentalGroupoid.mk (neighborhoodInclusion f x₀) := by
  intro h
  have hw : (w.as : Space f) = inclusion f x₀ := congrArg (fun z => z.as.1) h
  exact inclusion_not_mem_interiors f x₀ (hw ▸ w.as.property.2)

/-- Connectedness needed by the algebraic bridge follows from the established
neighborhood deformation, rather than being an extra assumption. -/
theorem neighborhood_groupoid_connected (f : ι → C(Circle, X)) (x₀ : X)
    [PathConnectedSpace X] (w : FundamentalGroupoid (puncturedNeighborhood f)) :
    Nonempty (FundamentalGroupoid.mk (neighborhoodInclusion f x₀) ⟶ w) := by
  let := neighborhood_pathConnectedSpace f x₀
  exact ⟨Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath _ _)⟩

/-- On the actual open neighborhood, the actual inclusion is surjective on
fundamental groups and has exactly the normal closure of the transported
half-circle relators as its kernel. The quotient equivalence commutes with this
inclusion; every geometry hypothesis is discharged by the constructed cover models. -/
theorem neighborhood_inclusion_vertex_quotient
    (f : ι → C(Circle, X)) (x₀ : X) [PathConnectedSpace X]
    (p : ∀ i : ι, Path (neighborhoodInclusion f x₀)
      (overlapLeft f (coverOverlapAnchor f i))) :
    let F := FundamentalGroup.map (neighborhoodToSpace f) (neighborhoodInclusion f x₀)
    let R := neighborhoodTransportedRelator f x₀ p
    Function.Surjective F ∧ F.ker = Subgroup.normalClosure (Set.range R) ∧
      ∃ E : FundamentalGroup (puncturedNeighborhood f) (neighborhoodInclusion f x₀) ⧸
          Subgroup.normalClosure (Set.range R) ≃* FundamentalGroup (Space f) (inclusion f x₀),
        ∀ g, E (QuotientGroup.mk' (Subgroup.normalClosure (Set.range R)) g) = F g := by
  let I := ULift.{u} ι
  let indexA : FundamentalGroupoid (overlap f) → I := fun w => ⟨overlapIndex f w.as⟩
  let indexC : FundamentalGroupoid (interiors f) → I := fun w => ⟨interiorIndex f w.as⟩
  let anchor : I → FundamentalGroupoid (overlap f) :=
    fun i => FundamentalGroupoid.mk (coverOverlapAnchor f i.down)
  let q : ∀ w : FundamentalGroupoid (overlap f), anchor (indexA w) ⟶ w :=
    fun w => Path.Homotopic.Quotient.mk (overlapAnchorPaths f w.as)
  let s : ∀ w : FundamentalGroupoid (interiors f),
      (FundamentalGroupoid.map (overlapRight f)).obj (anchor (indexC w)) ⟶ w :=
    fun w => Path.Homotopic.Quotient.mk (interiorAnchorPaths f w.as)
  let pI : ∀ i : I, FundamentalGroupoid.mk (neighborhoodInclusion f x₀) ⟶
      (FundamentalGroupoid.map (overlapLeft f)).obj (anchor i) :=
    fun i => Path.Homotopic.Quotient.mk (p i.down)
  let r : ∀ i : I, End (anchor i) := fun i => coverOverlapGeneratorClass f i.down
  have hindexC : ∀ (y z : FundamentalGroupoid (interiors f)) (_γ : y ⟶ z),
      indexC y = indexC z := by
    intro y z γ
    exact congrArg ULift.up (interiorIndex_arrow f γ)
  have hindex : ∀ w : FundamentalGroupoid (overlap f),
      indexC ((FundamentalGroupoid.map (overlapRight f)).obj w) = indexA w := by
    intro w
    exact congrArg ULift.up (interiorIndex_overlapToInteriors f w.as)
  have hcyc : ∀ (i : I) (g : End (anchor i)), ∃ n : ℤ, g = r i ^ n := by
    intro i g
    exact overlapAnchorGenerator_generates f i.down g
  have ht := pushout_vertex_quotient_of_component_data
    (FundamentalGroupoid.map (overlapLeft f)) (FundamentalGroupoid.map (overlapRight f))
    (FundamentalGroupoid.map (neighborhoodToSpace f)) (FundamentalGroupoid.map (interiorsToSpace f))
    (coverPushout f) (overlapLeft_groupoid_obj_injective f)
    (FundamentalGroupoid.mk (neighborhoodInclusion f x₀))
    (neighborhood_base_outside_overlap f x₀) (neighborhood_groupoid_connected f x₀)
    indexA indexC anchor q pI s (fun w => interiorVertexGroup_subsingleton f w.as)
    hindexC hindex r hcyc
  have hrange : Set.range (fun i : I => neighborhoodTransportedRelator f x₀ p i.down) =
      Set.range (neighborhoodTransportedRelator f x₀ p) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.down, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i⟩, rfl⟩
  change Function.Surjective
      (FundamentalGroup.map (neighborhoodToSpace f) (neighborhoodInclusion f x₀)) ∧
    (FundamentalGroup.map (neighborhoodToSpace f) (neighborhoodInclusion f x₀)).ker =
      Subgroup.normalClosure (Set.range (fun i : I => neighborhoodTransportedRelator f x₀ p i.down)) ∧
    ∃ E : FundamentalGroup (puncturedNeighborhood f) (neighborhoodInclusion f x₀) ⧸
        Subgroup.normalClosure (Set.range (fun i : I => neighborhoodTransportedRelator f x₀ p i.down)) ≃*
          FundamentalGroup (Space f) (inclusion f x₀), ∀ g,
      E (QuotientGroup.mk'
        (Subgroup.normalClosure (Set.range (fun i : I => neighborhoodTransportedRelator f x₀ p i.down))) g) =
        FundamentalGroup.map (neighborhoodToSpace f) (neighborhoodInclusion f x₀) g at ht
  obtain ⟨hsurj, hker, _⟩ := ht
  have hker' :
      (FundamentalGroup.map (neighborhoodToSpace f) (neighborhoodInclusion f x₀)).ker =
        Subgroup.normalClosure (Set.range (neighborhoodTransportedRelator f x₀ p)) := by
    simpa only [hrange] using hker
  exact ⟨hsurj, hker', quotientNormalClosureEquiv (neighborhoodTransportedRelator f x₀ p)
    (FundamentalGroup.map (neighborhoodToSpace f) (neighborhoodInclusion f x₀)) hsurj hker',
    fun _ => rfl⟩

/-- The original inclusion into the actual arbitrary two-cell attachment is
surjective on fundamental groups. This conclusion needs no choice of attaching
paths and follows through the proved neighborhood equivalence. -/
theorem inclusionPi1_surjective (f : ι → C(Circle, X)) (x₀ : X)
    [PathConnectedSpace X] : Function.Surjective (inclusionPi1 f x₀) := by
  let := neighborhood_pathConnectedSpace f x₀
  let p : ∀ i : ι, Path (neighborhoodInclusion f x₀)
      (overlapLeft f (coverOverlapAnchor f i)) :=
    fun i => PathConnectedSpace.somePath _ _
  obtain ⟨hsurj, _⟩ := neighborhood_inclusion_vertex_quotient f x₀ p
  intro g
  obtain ⟨h, hh⟩ := hsurj g
  obtain ⟨z, hz⟩ := (neighborhoodPi1Equiv f x₀).surjective h
  refine ⟨z, ?_⟩
  rw [← inclusionPi1_factorization]
  change FundamentalGroup.map (neighborhoodToSpace f) (neighborhoodInclusion f x₀)
    (neighborhoodPi1Equiv f x₀ z) = g
  rw [hz]
  exact hh

end CellAttachment
