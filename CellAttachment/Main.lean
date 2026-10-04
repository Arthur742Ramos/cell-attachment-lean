module

public import CellAttachment.GeometricPushout
public import CellAttachment.RelatorTransport
public import CellAttachment.EquivalenceExactness

@[expose] public section


/-!
# Attaching an arbitrary family of two-cells

The theorem concerns the genuine boundary-generated topological quotient and the
actual inclusion-induced map. All disk, annulus, retraction, cover and groupoid
pushout data are constructed in the imported proof modules.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The actual arbitrary-family cell attachment induces a surjective fundamental-group
map, with exactly the normal closure of the specified whiskered attaching loops as kernel. -/
theorem cell_attachment_exact (f : ι → C(Circle, X)) (x₀ : X) [PathConnectedSpace X]
    (γ : ∀ i, Path x₀ (f i 1)) :
    Function.Surjective (inclusionPi1 f x₀) ∧
      (inclusionPi1 f x₀).ker = attachingNormalClosure f x₀ γ := by
  let p := chosenAttachmentAnchorPath f x₀ γ
  obtain ⟨hs,hk,_⟩ := neighborhood_inclusion_vertex_quotient f x₀ p
  let e := neighborhoodPi1Equiv f x₀
  let r := attachingLoopClass f x₀ γ
  let F := FundamentalGroup.map (neighborhoodToSpace f) (neighborhoodInclusion f x₀)
  have hR : (fun i => e (r i)) = neighborhoodTransportedRelator f x₀ p := by
    funext i
    rw [neighborhoodTransportedRelator_path]
    exact neighborhoodPi1Equiv_attachingLoopClass f x₀ γ i
  have hk' : F.ker = Subgroup.normalClosure (Set.range (fun i => e (r i))) := by
    rw [hR]
    exact hk
  obtain ⟨hSurj,hKer⟩ := exact_comp_equiv e r F hs hk'
  have hFactor : F.comp e.toMonoidHom = inclusionPi1 f x₀ :=
    inclusionPi1_factorization f x₀
  rw [hFactor] at hSurj hKer
  exact ⟨hSurj,hKer⟩

/-- Full two-cell attachment theorem, including the inclusion-compatible quotient
isomorphism, for arbitrary independent space/index universes. -/
theorem two_cell_attachment : completeStatement.{u,v} := by
  intro X _ _ ι f x₀ γ
  obtain ⟨hs,hk⟩ := cell_attachment_exact f x₀ γ
  refine ⟨hs,hk,?_⟩
  refine ⟨quotientNormalClosureEquiv (attachingLoopClass f x₀ γ) (inclusionPi1 f x₀)
    hs hk, ?_⟩
  rfl

end CellAttachment
