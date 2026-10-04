module

public import CellAttachment.GroupQuotient

@[expose] public section


/-! # Transport of actual map exactness along a compatible group equivalence -/

namespace CellAttachment
universe u v w z
variable {G : Type u} {H : Type v} {K : Type w} {ι : Type z}
variable [Group G] [Group H] [Group K]

/-- The normal closure of a family transports under an actual group equivalence. -/
theorem mem_normalClosure_range_equiv (e : G ≃* H) (r : ι → G) (g : G) :
    e g ∈ Subgroup.normalClosure (Set.range (fun i => e (r i))) ↔
      g ∈ Subgroup.normalClosure (Set.range r) := by
  have hm := Subgroup.map_normalClosure (Set.range r) e.toMonoidHom e.surjective
  have hs : e.toMonoidHom '' Set.range r = Set.range (fun i => e (r i)) := by
    ext h
    simp
  rw [hs] at hm
  rw [← hm, Subgroup.mem_map]
  constructor
  · rintro ⟨a,ha,hag⟩
    exact e.injective hag ▸ ha
  · intro hg
    exact ⟨g,hg,rfl⟩

/-- Surjectivity and the precise kernel transport through a genuine compatible equivalence. -/
theorem exact_comp_equiv (e : G ≃* H) (r : ι → G) (p : H →* K)
    (hp : Function.Surjective p)
    (hker : p.ker = Subgroup.normalClosure (Set.range (fun i => e (r i)))) :
    Function.Surjective (p.comp e.toMonoidHom) ∧
      (p.comp e.toMonoidHom).ker = Subgroup.normalClosure (Set.range r) := by
  constructor
  · exact hp.comp e.surjective
  · ext g
    change p (e g) = 1 ↔ g ∈ Subgroup.normalClosure (Set.range r)
    rw [← MonoidHom.mem_ker, hker]
    exact mem_normalClosure_range_equiv e r g

end CellAttachment
