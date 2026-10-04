/-
Attaching arbitrary families of two-cells, Hatcher Proposition 1.26.
Authors: Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz.
First-party sources released under Apache-2.0.
Vendored sources preserve their original license and copyright notices below.
-/
/-
Vendored directed-topology helpers retain the following MIT notice.
Copyright 2023 Dominique Lawson
Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-/
module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Constructions
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Tactic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homotopy.Equiv
@[expose] public section
/-! Source module: CellAttachment.GroupQuotient -/
section CellAttachment_GroupQuotient
/-!
# Algebraic quotient tools for cell attachment
This file contains only group-theoretic results. In particular, it does not assume or
claim that any topological attachment induces a surjective fundamental-group map or
has a specified kernel. Once those geometric assertions have been established, the
results here produce the quotient equivalence and its compatibility with the map.
-/
namespace CellAttachment
universe u v w
variable {G : Type u} [Group G] {H : Type v} [Group H] {ι : Type w}
/-- Killing every member of a family is equivalent to killing its normal closure. -/
theorem normalClosure_range_le_ker_iff (r : ι → G) (f : G →* H) :
    Subgroup.normalClosure (Set.range r) ≤ f.ker ↔ ∀ i, f (r i) = 1 := by
  constructor
  · intro h i
    exact MonoidHom.mem_ker.mp (h (Subgroup.subset_normalClosure (Set.mem_range_self i)))
  · intro h
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact MonoidHom.mem_ker.mpr (h i)
/-- A homomorphism killing the relators descends to the quotient by their normal closure. -/
def liftNormalClosure (r : ι → G) (f : G →* H) (h : ∀ i, f (r i) = 1) :
    G ⧸ Subgroup.normalClosure (Set.range r) →* H :=
  QuotientGroup.lift _ f ((normalClosure_range_le_ker_iff r f).mpr h)
@[simp]
theorem liftNormalClosure_mk (r : ι → G) (f : G →* H) (h : ∀ i, f (r i) = 1)
    (g : G) :
    liftNormalClosure r f h (QuotientGroup.mk' (Subgroup.normalClosure (Set.range r)) g) =
      f g := rfl
/-- The descended homomorphism commutes with the quotient projection. -/
@[simp]
theorem liftNormalClosure_comp_mk (r : ι → G) (f : G →* H) (h : ∀ i, f (r i) = 1) :
    (liftNormalClosure r f h).comp
      (QuotientGroup.mk' (Subgroup.normalClosure (Set.range r))) = f := rfl
/-- The descended homomorphism is uniquely determined by this compatibility. -/
theorem liftNormalClosure_unique (r : ι → G) (f : G →* H) (h : ∀ i, f (r i) = 1)
    (k : G ⧸ Subgroup.normalClosure (Set.range r) →* H)
    (hk : k.comp (QuotientGroup.mk' (Subgroup.normalClosure (Set.range r))) = f) :
    k = liftNormalClosure r f h := by
  apply QuotientGroup.monoidHom_ext
  rw [hk, liftNormalClosure_comp_mk]
/-- The compatible first-isomorphism equivalence, after a surjective map and its
kernel have been identified by a separate argument. -/
noncomputable def quotientNormalClosureEquiv (r : ι → G) (f : G →* H)
    (hf : Function.Surjective f) (hker : f.ker = Subgroup.normalClosure (Set.range r)) :
    G ⧸ Subgroup.normalClosure (Set.range r) ≃* H :=
  QuotientGroup.liftEquiv _ hf hker.symm
@[simp]
theorem quotientNormalClosureEquiv_mk (r : ι → G) (f : G →* H)
    (hf : Function.Surjective f) (hker : f.ker = Subgroup.normalClosure (Set.range r))
    (g : G) :
    quotientNormalClosureEquiv r f hf hker
      (QuotientGroup.mk' (Subgroup.normalClosure (Set.range r)) g) = f g := rfl
/-- Compatibility in homomorphism form, suitable for a commutative diagram. -/
@[simp]
theorem quotientNormalClosureEquiv_comp_mk (r : ι → G) (f : G →* H)
    (hf : Function.Surjective f) (hker : f.ker = Subgroup.normalClosure (Set.range r)) :
    (quotientNormalClosureEquiv r f hf hker).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.normalClosure (Set.range r))) = f := rfl
/-- Exactness identifies precisely which elements the original map kills. -/
theorem map_eq_one_iff_mem_normalClosure (r : ι → G) (f : G →* H)
    (hker : f.ker = Subgroup.normalClosure (Set.range r)) (g : G) :
    f g = 1 ↔ g ∈ Subgroup.normalClosure (Set.range r) := by
  rw [← hker]
  exact MonoidHom.mem_ker.symm
/-- Independently replacing the generators by conjugate elements does not change
normal closure. This is the algebraic part of independence from whiskering paths. -/
theorem normalClosure_range_eq_of_isConj (r s : ι → G)
    (h : ∀ i, IsConj (r i) (s i)) :
    Subgroup.normalClosure (Set.range r) = Subgroup.normalClosure (Set.range s) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact Subgroup.conjugatesOfSet_subset_normalClosure
      (Group.mem_conjugatesOfSet_iff.mpr ⟨s i, Set.mem_range_self i, (h i).symm⟩)
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact Subgroup.conjugatesOfSet_subset_normalClosure
      (Group.mem_conjugatesOfSet_iff.mpr ⟨r i, Set.mem_range_self i, h i⟩)
/-- A separate conjugating element may be chosen for every generator. -/
theorem normalClosure_range_conjugate (r c : ι → G) :
    Subgroup.normalClosure (Set.range (fun i => c i * r i * (c i)⁻¹)) =
      Subgroup.normalClosure (Set.range r) := by
  symm
  apply normalClosure_range_eq_of_isConj
  intro i
  exact isConj_iff.mpr ⟨c i, rfl⟩
/-- The normal closure is also independent of the orientation of all generators. -/
theorem normalClosure_range_inverse (r : ι → G) :
    Subgroup.normalClosure (Set.range (fun i => (r i)⁻¹)) =
      Subgroup.normalClosure (Set.range r) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact (Subgroup.normalClosure (Set.range r)).inv_mem
      (Subgroup.subset_normalClosure (Set.mem_range_self i))
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    have h : (r i)⁻¹ ∈ Subgroup.normalClosure (Set.range (fun j => (r j)⁻¹)) :=
      Subgroup.subset_normalClosure (Set.mem_range_self i)
    exact (Subgroup.inv_mem_iff _).mp h
/-- Changing independently chosen conjugating paths induces the identity-on-
representatives equivalence between the corresponding quotient groups. -/
def quotientNormalClosureConjugateEquiv (r c : ι → G) :
    G ⧸ Subgroup.normalClosure (Set.range (fun i => c i * r i * (c i)⁻¹)) ≃*
      G ⧸ Subgroup.normalClosure (Set.range r) :=
  QuotientGroup.quotientMulEquivOfEq (normalClosure_range_conjugate r c)
@[simp]
theorem quotientNormalClosureConjugateEquiv_mk (r c : ι → G) (g : G) :
    quotientNormalClosureConjugateEquiv r c
      (QuotientGroup.mk' (Subgroup.normalClosure
        (Set.range (fun i => c i * r i * (c i)⁻¹))) g) =
      QuotientGroup.mk' (Subgroup.normalClosure (Set.range r)) g := rfl
end CellAttachment
end CellAttachment_GroupQuotient
/-! Source module: CellAttachment.GroupoidQuotient -/
section CellAttachment_GroupoidQuotient
/-!
# Vertex-group tools for a categorical van Kampen square
These are abstract groupoid lemmas. They do not assert that a particular cell-attachment
space has the required open cover, connectivity, or disk and annulus homotopy types.
-/
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace CellAttachment
universe u v
variable {W U V P : Type u}
variable [Groupoid.{v} W] [Groupoid.{v} U] [Groupoid.{v} V] [Groupoid.{v} P]
/-- Changing the vertex of a groupoid by a chosen path is a group isomorphism. -/
noncomputable def transportEnd {a b : U} (p : a ⟶ b) : End b ≃* End a where
  toFun g := p ≫ g ≫ inv p
  invFun g := inv p ≫ g ≫ p
  left_inv g := by simp [Category.assoc]
  right_inv g := by simp [Category.assoc]
  map_mul' g h := by simp [End.mul_def, Category.assoc]
/-- A loop at an overlap vertex, transported to the chosen vertex on the left. -/
noncomputable def overlapLoop (i : W ⥤ U) (b : U) (w : W)
    (p : b ⟶ i.obj w) (g : End w) : End b :=
  transportEnd p (i.map g)
/-- Equality of functors transports the assertion that an endomorphism is trivial. -/
theorem map_eq_id_of_functor_eq {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F G : C ⥤ D) (h : F = G) (x : C) (a : End x)
    (ha : G.map a = 𝟙 (G.obj x)) : F.map a = 𝟙 (F.obj x) := by
  subst G
  exact ha
/-- The commutative square kills transported overlap loops whenever the right-hand
vertex group is trivial. Only commutativity, rather than the universal property,
is needed for this direction. -/
theorem map_overlapLoop_eq_one (i : W ⥤ U) (k : W ⥤ V)
    (j : U ⥤ P) (l : V ⥤ P) (h : i ⋙ j = k ⋙ l)
    (b : U) (w : W) (p : b ⟶ i.obj w) (g : End w)
    (hg : k.map g = 𝟙 (k.obj w)) :
    j.mapEnd b (overlapLoop i b w p g) = 1 := by
  have hh : j.map (i.map g) = 𝟙 (j.obj (i.obj w)) := by
    exact map_eq_id_of_functor_eq (i ⋙ j) (k ⋙ l) h w g
      (by change l.map (k.map g) = 𝟙 (l.obj (k.obj w)); rw [hg, l.map_id])
  simp [overlapLoop, transportEnd, Functor.map_comp, hh]
/-- A Cat pushout with simply connected right-hand components kills the normal
closure of any chosen family of transported overlap loops. This is a proved
kernel inclusion, not an assumption identifying the entire kernel. -/
theorem normalClosure_overlapLoops_le_ker (i : W ⥤ U) (k : W ⥤ V)
    (j : U ⥤ P) (l : V ⥤ P)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (hV : ∀ v : V, Subsingleton (End v))
    (b : U) {ι : Type u} (w : ι → W)
    (p : ∀ a, b ⟶ i.obj (w a)) (r : ∀ a, End (w a)) :
    Subgroup.normalClosure (Set.range (fun a => overlapLoop i b (w a) (p a) (r a))) ≤
      (j.mapEnd b).ker := by
  apply (normalClosure_range_le_ker_iff _ _).mpr
  intro a
  apply map_overlapLoop_eq_one i k j l
    (congrArg Cat.Hom.toFunctor h.w) b (w a) (p a) (r a)
  exact (hV (k.obj (w a))).elim _ _
/-- Any compatible functor out of the left-hand groupoid detects relations in
its vertex group: relations imposed by the pushout must also hold in its target. -/
theorem pushout_kernel_le_kernel {D : Type u} [Category.{v} D]
    (i : W ⥤ U) (k : W ⥤ V) (j : U ⥤ P) (l : V ⥤ P)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (F : U ⥤ D) (K : V ⥤ D) (hFK : i ⋙ F = k ⋙ K) (b : U) :
    (j.mapEnd b).ker ≤ (F.mapEnd b).ker := by
  let d : P ⥤ D := (h.desc F.toCatHom K.toCatHom
    (Cat.ext hFK)).toFunctor
  have hd : j ⋙ d = F :=
    congrArg Cat.Hom.toFunctor (h.inl_desc F.toCatHom K.toCatHom (Cat.ext hFK))
  intro g hg
  apply MonoidHom.mem_ker.mpr
  change F.map g = 𝟙 (F.obj b)
  apply map_eq_id_of_functor_eq F (j ⋙ d) hd.symm b g
  change d.map (j.map g) = 𝟙 (d.obj (j.obj b))
  have hg' : j.map g = 𝟙 (j.obj b) := MonoidHom.mem_ker.mp hg
  rw [hg']
  exact d.map_id _
/-- Cyclic overlap vertex groups reduce every overlap-coordinate calculation
to killing the transported generator. The two overlap vertices may be joined
to a common component representative by different chosen paths. -/
theorem overlap_coordinate_eq_one_of_cyclic
    (i : W ⥤ U) (b : U) (w₀ x y : W) (a : b ⟶ i.obj w₀)
    (p : w₀ ⟶ x) (s : w₀ ⟶ y) (f : x ⟶ y) (r : End w₀)
    (hcyc : ∀ g : End w₀, ∃ n : ℤ, g = r ^ n)
    {G : Type v} [Group G] (q : End b →* G)
    (hr : q (overlapLoop i b w₀ a r) = 1) :
    q ((a ≫ i.map p) ≫ i.map f ≫ inv (a ≫ i.map s)) = 1 := by
  let e : End w₀ →* End b := (transportEnd a).toMonoidHom.comp (i.mapEnd w₀)
  have hcoord : ((a ≫ i.map p) ≫ i.map f ≫ inv (a ≫ i.map s) : End b) =
      e (p ≫ f ≫ inv s) := by
    simp [e, transportEnd, Functor.map_comp, Category.assoc]
  rw [hcoord]
  obtain ⟨n, hn⟩ := hcyc (p ≫ f ≫ inv s)
  rw [hn, e.map_zpow, q.map_zpow]
  change q (overlapLoop i b w₀ a r) ^ n = 1
  rw [hr, one_zpow]
attribute [local instance] uliftCategory
/-- The one-object groupoid placed in the object universe of the van Kampen
square. Its morphisms are still the elements of `G`. -/
abbrev VertexTarget (G : Type v) [Group G] := ULift.{u} (SingleObj G)
/-- A choice of paths from a vertex turns a homomorphism on its vertex group
into a functor on the whole connected groupoid. -/
noncomputable def basedFunctor (b : U) (p : ∀ x : U, b ⟶ x)
    {G : Type v} [Group G] (q : End b →* G) : U ⥤ VertexTarget.{u,v} G where
  obj _ := ⟨SingleObj.star G⟩
  map {x y} f := q (p x ≫ f ≫ inv (p y))
  map_id x := by
    change q (p x ≫ 𝟙 x ≫ inv (p x)) = 1
    simpa using q.map_one
  map_comp {x y z} f g := by
    change q (p x ≫ (f ≫ g) ≫ inv (p z)) =
      q (p y ≫ g ≫ inv (p z)) * q (p x ≫ f ≫ inv (p y))
    rw [← q.map_mul]
    simp [End.mul_def, Category.assoc]
/-- At the chosen vertex, normalized chosen paths recover the original group
homomorphism exactly. -/
theorem basedFunctor_map_base (b : U) (p : ∀ x : U, b ⟶ x)
    (hp : p b = 𝟙 b) {G : Type v} [Group G] (q : End b →* G) (g : End b) :
    (basedFunctor b p q).map g = q g := by
  simp [basedFunctor, hp]
/-- The based functor has precisely the original homomorphism's kernel. -/
theorem basedFunctor_ker (b : U) (p : ∀ x : U, b ⟶ x)
    (hp : p b = 𝟙 b) {G : Type v} [Group G] (q : End b →* G) :
    ((basedFunctor b p q).mapEnd b).ker = q.ker := by
  ext g
  change (basedFunctor b p q).map g = 1 ↔ q g = 1
  rw [basedFunctor_map_base b p hp q]
/-- If every arrow in the overlap becomes trivial in the quotient-coordinate
functor, it agrees there with the constant functor on the right-hand groupoid.
This condition is the concrete remaining annulus calculation, not a claim
that the attachment theorem is already established. -/
theorem basedFunctor_overlap_eq_const (i : W ⥤ U) (k : W ⥤ V)
    (b : U) (p : ∀ x : U, b ⟶ x) {G : Type v} [Group G] (q : End b →* G)
    (hoverlap : ∀ (x y : W) (f : x ⟶ y),
      q (p (i.obj x) ≫ i.map f ≫ inv (p (i.obj y))) = 1) :
    i ⋙ basedFunctor b p q =
      k ⋙ (Functor.const V).obj (ULift.up (SingleObj.star G)) := by
  apply Functor.hext
  · intro x
    rfl
  · intro x y f
    apply heq_of_eq
    exact hoverlap x y f
/-- A Cat pushout gives the reverse kernel inclusion without assuming a
surjective vertex-group map. The geometric inputs still required are normalized
paths in the left groupoid and the explicit quotient calculation on overlap arrows. -/
theorem pushout_kernel_le_normalClosure
    (i : W ⥤ U) (k : W ⥤ V) (j : U ⥤ P) (l : V ⥤ P)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (b : U) (p : ∀ x : U, b ⟶ x) (hp : p b = 𝟙 b)
    {ι : Type u} (r : ι → End b)
    (hoverlap : ∀ (x y : W) (f : x ⟶ y),
      QuotientGroup.mk' (Subgroup.normalClosure (Set.range r))
        (p (i.obj x) ≫ i.map f ≫ inv (p (i.obj y))) = 1) :
    (j.mapEnd b).ker ≤ Subgroup.normalClosure (Set.range r) := by
  let N := Subgroup.normalClosure (Set.range r)
  let q : End b →* End b ⧸ N := QuotientGroup.mk' N
  have hle := pushout_kernel_le_kernel i k j l h (basedFunctor b p q)
    ((Functor.const V).obj (ULift.up (SingleObj.star (End b ⧸ N))))
    (basedFunctor_overlap_eq_const i k b p q hoverlap) b
  rw [basedFunctor_ker b p hp q] at hle
  change (j.mapEnd b).ker ≤ (QuotientGroup.mk' N).ker at hle
  rw [QuotientGroup.ker_mk'] at hle
  exact hle
section ArrowDescent
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
/-- A natural transformation regarded as a functor into the arrow category. -/
def natTransArrow {F G : C ⥤ D} (a : F ⟶ G) : C ⥤ Arrow D where
  obj x := Arrow.mk (a.app x)
  map f := Arrow.homMk (F.map f) (G.map f) (a.naturality f)
  map_id x := by
    apply Arrow.hom_ext <;> simp
  map_comp f g := by
    apply Arrow.hom_ext <;> simp
@[simp] theorem natTransArrow_left {F G : C ⥤ D} (a : F ⟶ G) :
    natTransArrow a ⋙ Arrow.leftFunc = F := rfl
@[simp] theorem natTransArrow_right {F G : C ⥤ D} (a : F ⟶ G) :
    natTransArrow a ⋙ Arrow.rightFunc = G := rfl
/-- Natural transformations glue across a strict categorical pushout. Encoding
them by functors into an arrow category derives this from the ordinary universal
property, rather than assuming a bicategorical pushout theorem. -/
theorem pushout_natTrans_exists
    {A B C D E : Type u} [Category.{u} A] [Category.{u} B]
    [Category.{u} C] [Category.{u} D] [Category.{u} E]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (F G : D ⥤ E) (a : j ⋙ F ⟶ j ⋙ G) (b : l ⋙ F ⟶ l ⋙ G)
    (hab : i ⋙ natTransArrow a = k ⋙ natTransArrow b) :
    ∃ t : F ⟶ G, whiskerLeft j t = a ∧ whiskerLeft l t = b := by
  let d : D ⥤ Arrow E := (h.desc (natTransArrow a).toCatHom
    (natTransArrow b).toCatHom (Cat.ext hab)).toFunctor
  have hdj : j ⋙ d = natTransArrow a :=
    congrArg Cat.Hom.toFunctor (h.inl_desc (natTransArrow a).toCatHom (natTransArrow b).toCatHom (Cat.ext hab))
  have hdl : l ⋙ d = natTransArrow b :=
    congrArg Cat.Hom.toFunctor (h.inr_desc (natTransArrow a).toCatHom (natTransArrow b).toCatHom (Cat.ext hab))
  have hF : d ⋙ Arrow.leftFunc = F := by
    apply (Functor.equivCatHom D E).injective
    apply h.hom_ext
    · apply Cat.ext
      change (j ⋙ d) ⋙ Arrow.leftFunc = j ⋙ F
      rw [hdj, natTransArrow_left]
    · apply Cat.ext
      change (l ⋙ d) ⋙ Arrow.leftFunc = l ⋙ F
      rw [hdl, natTransArrow_left]
  have hG : d ⋙ Arrow.rightFunc = G := by
    apply (Functor.equivCatHom D E).injective
    apply h.hom_ext
    · apply Cat.ext
      change (j ⋙ d) ⋙ Arrow.rightFunc = j ⋙ G
      rw [hdj, natTransArrow_right]
    · apply Cat.ext
      change (l ⋙ d) ⋙ Arrow.rightFunc = l ⋙ G
      rw [hdl, natTransArrow_right]
  let t : F ⟶ G := eqToHom hF.symm ≫ whiskerLeft d Arrow.leftToRight ≫ eqToHom hG
  refine ⟨t, ?_, ?_⟩
  · ext x
    have he : Arrow.mk (d.obj (j.obj x)).hom = Arrow.mk (a.app x) := by
      rw [Arrow.mk_eq]
      exact Functor.congr_obj hdj x
    obtain ⟨hx, hy, hh⟩ := (Arrow.mk_eq_mk_iff _ _).mp he
    dsimp [t]
    simp only [eqToHom_app, Arrow.leftToRight_app]
    rw [hh]
    cat_disch
  · ext x
    have he : Arrow.mk (d.obj (l.obj x)).hom = Arrow.mk (b.app x) := by
      rw [Arrow.mk_eq]
      exact Functor.congr_obj hdl x
    obtain ⟨hx, hy, hh⟩ := (Arrow.mk_eq_mk_iff _ _).mp he
    dsimp [t]
    simp only [eqToHom_app, Arrow.leftToRight_app]
    rw [hh]
    cat_disch
/-- Interpret a group homomorphism into a vertex group as a constant-object
functor from the universe-lifted one-object groupoid. -/
def vertexFunctor {D : Type u} [Category.{u} D] (x : D)
    {Q : Type u} [Group Q] (e : Q →* End x) : VertexTarget.{u,u} Q ⥤ D where
  obj _ := x
  map f := e f
  map_id _ := e.map_one
  map_comp f g := e.map_mul g f
/-- A glued, basepoint-normalized contraction proves surjectivity of the actual
left inclusion on vertex groups. Its hypotheses are functors and compatible
path transformations, not surjectivity or a prescribed kernel for that map. -/
theorem pushout_mapEnd_surjective_of_contraction
    {A B C D : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (x : B) {Q : Type u} [Group Q] (q : End x →* Q)
    (hq : Function.Surjective q) (e : Q →* End (j.obj x))
    (he : e.comp q = j.mapEnd x) (d : D ⥤ VertexTarget.{u,u} Q)
    (a : j ⋙ (d ⋙ vertexFunctor (j.obj x) e) ⟶ j ⋙ 𝟭 D)
    (b : l ⋙ (d ⋙ vertexFunctor (j.obj x) e) ⟶ l ⋙ 𝟭 D)
    (hab : i ⋙ natTransArrow a = k ⋙ natTransArrow b)
    (ha : a.app x = 𝟙 (j.obj x)) : Function.Surjective (j.mapEnd x) := by
  obtain ⟨t, ht, _⟩ := pushout_natTrans_exists i k j l h
    (d ⋙ vertexFunctor (j.obj x) e) (𝟭 D) a b hab
  have htbase : t.app (j.obj x) = 𝟙 (j.obj x) := by
    have hh := congrArg (fun s => s.app x) ht
    exact hh.trans ha
  intro g
  have hn := t.naturality g
  change e (d.map g) ≫ t.app (j.obj x) = t.app (j.obj x) ≫ g at hn
  rw [htbase] at hn
  have hn' : e (d.map g) = g :=
    (Category.comp_id (e (d.map g))).symm.trans (hn.trans (Category.id_comp g))
  obtain ⟨z, hz⟩ := hq (d.map g)
  refine ⟨z, ?_⟩
  have hez := DFunLike.congr_fun he z
  change e (q z) = j.map z at hez
  change j.map z = g
  rw [← hez, hz]
  exact hn'
/-- Paths on the left provide the local contraction of the quotient
reconstruction functor. -/
noncomputable def reconstructionLeft
    {B D : Type u} [Groupoid.{u} B] [Groupoid.{u} D]
    (j : B ⥤ D) (x : B) (p : ∀ y : B, x ⟶ y)
    {Q : Type u} [Group Q] (q : End x →* Q) (e : Q →* End (j.obj x))
    (he : e.comp q = j.mapEnd x) (d : D ⥤ VertexTarget.{u,u} Q)
    (hd : j ⋙ d = basedFunctor x p q) :
    j ⋙ (d ⋙ vertexFunctor (j.obj x) e) ⟶ j ⋙ 𝟭 D where
  app y := j.map (p y)
  naturality y z f := by
    change e (d.map (j.map f)) ≫ j.map (p z) = j.map (p y) ≫ j.map f
    have hm : d.map (j.map f) = q (p y ≫ f ≫ inv (p z)) :=
      congrArg (fun T : B ⥤ VertexTarget.{u,u} Q => (T.map f : Q)) hd
    have he' := DFunLike.congr_fun he (p y ≫ f ≫ inv (p z))
    change e (q (p y ≫ f ≫ inv (p z))) = j.map (p y ≫ f ≫ inv (p z)) at he'
    rw [hm, he', ← j.map_comp, ← j.map_comp]
    congr 1
    simp [Category.assoc]
/-- Paths on a simply connected right-hand component provide its local
contraction. Naturality of the chosen paths is a concrete groupoid condition. -/
noncomputable def reconstructionRight
    {B C D : Type u} [Groupoid.{u} B] [Groupoid.{u} C] [Groupoid.{u} D]
    (j : B ⥤ D) (l : C ⥤ D) (x : B) {Q : Type u} [Group Q]
    (e : Q →* End (j.obj x)) (d : D ⥤ VertexTarget.{u,u} Q)
    (hd : l ⋙ d = (Functor.const C).obj (ULift.up (SingleObj.star Q)))
    (p : ∀ y : C, j.obj x ⟶ l.obj y)
    (hp : ∀ (y z : C) (f : y ⟶ z), p y ≫ l.map f = p z) :
    l ⋙ (d ⋙ vertexFunctor (j.obj x) e) ⟶ l ⋙ 𝟭 D where
  app y := p y
  naturality y z f := by
    change e (d.map (l.map f)) ≫ p z = p y ≫ l.map f
    have hm : d.map (l.map f) = (1 : Q) :=
      congrArg (fun T : C ⥤ VertexTarget.{u,u} Q => (T.map f : Q)) hd
    rw [hm, e.map_one]
    change 𝟙 (j.obj x) ≫ p z = p y ≫ l.map f
    rw [Category.id_comp]
    exact (hp y z f).symm
/-- Local path contractions agree on the overlap when their chosen paths
agree there. Endpoint transports are recorded as heterogeneous equality. -/
theorem reconstruction_overlap
    {A B C D : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (hc : i ⋙ j = k ⋙ l) (x : B) (p : ∀ y : B, x ⟶ y)
    {Q : Type u} [Group Q] (q : End x →* Q) (e : Q →* End (j.obj x))
    (he : e.comp q = j.mapEnd x) (d : D ⥤ VertexTarget.{u,u} Q)
    (hdj : j ⋙ d = basedFunctor x p q)
    (hdl : l ⋙ d = (Functor.const C).obj (ULift.up (SingleObj.star Q)))
    (c : ∀ y : C, j.obj x ⟶ l.obj y)
    (hn : ∀ (y z : C) (f : y ⟶ z), c y ≫ l.map f = c z)
    (hw : ∀ w : A, HEq (j.map (p (i.obj w))) (c (k.obj w))) :
    i ⋙ natTransArrow (reconstructionLeft j x p q e he d hdj) =
      k ⋙ natTransArrow (reconstructionRight j l x e d hdl c hn) := by
  let objEq : ∀ w : A,
      (i ⋙ natTransArrow (reconstructionLeft j x p q e he d hdj)).obj w =
        (k ⋙ natTransArrow (reconstructionRight j l x e d hdl c hn)).obj w := fun w => by
    change Arrow.mk (j.map (p (i.obj w))) = Arrow.mk (c (k.obj w))
    apply Arrow.ext (f := Arrow.mk (j.map (p (i.obj w))))
      (g := Arrow.mk (c (k.obj w))) rfl (Functor.congr_obj hc w)
    exact (conj_eqToHom_iff_heq _ _ rfl (Functor.congr_obj hc w)).mpr (hw w)
  refine CategoryTheory.Functor.ext objEq ?_
  intro w z f
  apply Arrow.hom_ext
  · simp only [Arrow.comp_left, Arrow.eqToHom_left]
    have hm := congrArg (fun T : A ⥤ D => e (d.map (T.map f))) hc
    simpa only [Functor.comp_map, natTransArrow, reconstructionLeft,
      reconstructionRight, vertexFunctor, Arrow.homMk_left, eqToHom_refl, Category.id_comp,
      Category.comp_id] using hm
  · simp only [Arrow.comp_right, Arrow.eqToHom_right]
    change j.map (i.map f) = eqToHom (Functor.congr_obj hc w) ≫
      l.map (k.map f) ≫ eqToHom (Functor.congr_obj hc z).symm
    exact Functor.congr_hom hc f
/-- Explicit path-coordinate criterion for surjectivity of the left inclusion
in a groupoid pushout. All the assumptions are local functors, group
homomorphisms, and chosen paths on the two sides and their overlap. -/
theorem pushout_mapEnd_surjective_of_path_coordinates
    {A B C D : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (x : B) (p : ∀ y : B, x ⟶ y) (hp : p x = 𝟙 x)
    {Q : Type u} [Group Q] (q : End x →* Q) (hq : Function.Surjective q)
    (e : Q →* End (j.obj x)) (he : e.comp q = j.mapEnd x)
    (hoverlap : ∀ (y z : A) (f : y ⟶ z),
      q (p (i.obj y) ≫ i.map f ≫ inv (p (i.obj z))) = 1)
    (c : ∀ y : C, j.obj x ⟶ l.obj y)
    (hn : ∀ (y z : C) (f : y ⟶ z), c y ≫ l.map f = c z)
    (hw : ∀ w : A, HEq (j.map (p (i.obj w))) (c (k.obj w))) :
    Function.Surjective (j.mapEnd x) := by
  have hcompat := basedFunctor_overlap_eq_const i k x p q hoverlap
  let d : D ⥤ VertexTarget.{u,u} Q := (h.desc (basedFunctor x p q).toCatHom
    ((Functor.const C).obj (ULift.up (SingleObj.star Q))).toCatHom
    (Cat.ext hcompat)).toFunctor
  have hdj : j ⋙ d = basedFunctor x p q :=
    congrArg Cat.Hom.toFunctor (h.inl_desc (basedFunctor x p q).toCatHom
      ((Functor.const C).obj (ULift.up (SingleObj.star Q))).toCatHom (Cat.ext hcompat))
  have hdl : l ⋙ d = (Functor.const C).obj (ULift.up (SingleObj.star Q)) :=
    congrArg Cat.Hom.toFunctor (h.inr_desc (basedFunctor x p q).toCatHom
      ((Functor.const C).obj (ULift.up (SingleObj.star Q))).toCatHom (Cat.ext hcompat))
  apply pushout_mapEnd_surjective_of_contraction i k j l h x q hq e he d
    (reconstructionLeft j x p q e he d hdj)
    (reconstructionRight j l x e d hdl c hn)
  · exact reconstruction_overlap i k j l (congrArg Cat.Hom.toFunctor h.w)
      x p q e he d hdj hdl c hn hw
  · change j.map (p x) = 𝟙 (j.obj x)
    rw [hp, j.map_id]
/-- Exactness of the inclusion map is derived from the categorical pushout
and explicit path coordinates. No surjectivity or kernel equality for the
inclusion is assumed. The relator-killing and overlap-coordinate hypotheses
must be established from the disk/annulus geometry before applying this lemma. -/
theorem pushout_exact_of_path_coordinates
    {A B C D : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (x : B) (p : ∀ y : B, x ⟶ y) (hp : p x = 𝟙 x)
    {ι : Type u} (r : ι → End x) (hr : ∀ a, j.mapEnd x (r a) = 1)
    (hoverlap : ∀ (y z : A) (f : y ⟶ z),
      QuotientGroup.mk' (Subgroup.normalClosure (Set.range r))
        (p (i.obj y) ≫ i.map f ≫ inv (p (i.obj z))) = 1)
    (c : ∀ y : C, j.obj x ⟶ l.obj y)
    (hn : ∀ (y z : C) (f : y ⟶ z), c y ≫ l.map f = c z)
    (hw : ∀ w : A, HEq (j.map (p (i.obj w))) (c (k.obj w))) :
    Function.Surjective (j.mapEnd x) ∧
      (j.mapEnd x).ker = Subgroup.normalClosure (Set.range r) := by
  constructor
  · exact pushout_mapEnd_surjective_of_path_coordinates i k j l h x p hp
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (liftNormalClosure r (j.mapEnd x) hr)
      (liftNormalClosure_comp_mk r (j.mapEnd x) hr) hoverlap c hn hw
  · apply le_antisymm
    · exact pushout_kernel_le_normalClosure i k j l h x p hp r hoverlap
    · exact (normalClosure_range_le_ker_iff r (j.mapEnd x)).mpr hr
/-- The path-coordinate criterion yields a quotient isomorphism that commutes
with the actual inclusion on every loop. -/
theorem pushout_quotient_equiv_of_path_coordinates
    {A B C D : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (x : B) (p : ∀ y : B, x ⟶ y) (hp : p x = 𝟙 x)
    {ι : Type u} (r : ι → End x) (hr : ∀ a, j.mapEnd x (r a) = 1)
    (hoverlap : ∀ (y z : A) (f : y ⟶ z),
      QuotientGroup.mk' (Subgroup.normalClosure (Set.range r))
        (p (i.obj y) ≫ i.map f ≫ inv (p (i.obj z))) = 1)
    (c : ∀ y : C, j.obj x ⟶ l.obj y)
    (hn : ∀ (y z : C) (f : y ⟶ z), c y ≫ l.map f = c z)
    (hw : ∀ w : A, HEq (j.map (p (i.obj w))) (c (k.obj w))) :
    ∃ E : End x ⧸ Subgroup.normalClosure (Set.range r) ≃* End (j.obj x),
      ∀ g : End x, E (QuotientGroup.mk' (Subgroup.normalClosure (Set.range r)) g) =
        j.mapEnd x g := by
  obtain ⟨hsurj, hker⟩ := pushout_exact_of_path_coordinates i k j l h x p hp r hr
    hoverlap c hn hw
  exact ⟨quotientNormalClosureEquiv r (j.mapEnd x) hsurj hker, fun _ => rfl⟩
/-- Chosen paths from a vertex can always be normalized at that vertex. -/
noncomputable def normalizedPaths
    {B : Type u} [Groupoid.{u} B] (x : B) (hB : ∀ y : B, Nonempty (x ⟶ y)) :
    ∀ y : B, x ⟶ y := by
  classical
  exact fun y => if h : x = y then eqToHom h else Classical.choice (hB y)
@[simp] theorem normalizedPaths_self
    {B : Type u} [Groupoid.{u} B] (x : B) (hB : ∀ y : B, Nonempty (x ⟶ y)) :
    normalizedPaths x hB x = 𝟙 x := by
  classical
  simp [normalizedPaths]
/-- Extend prescribed anchor-to-overlap paths to all left-hand objects. The
object embedding prevents different overlap prescriptions from colliding. -/
noncomputable def overlapCoordinates
    {A B I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    (i : A ⥤ B) (x : B) (index : A → I) (anchor : I → A)
    (q : ∀ w : A, anchor (index w) ⟶ w)
    (p : ∀ a : I, x ⟶ i.obj (anchor a)) (fallback : ∀ y : B, x ⟶ y) :
    ∀ y : B, x ⟶ y := by
  classical
  exact fun y => if h : ∃ w : A, i.obj w = y then
    p (index (Classical.choose h)) ≫ i.map (q (Classical.choose h)) ≫
      eqToHom (Classical.choose_spec h)
    else fallback y
theorem overlapCoordinates_on_overlap
    {A B I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    (i : A ⥤ B) (hi : Function.Injective i.obj) (x : B)
    (index : A → I) (anchor : I → A) (q : ∀ w : A, anchor (index w) ⟶ w)
    (p : ∀ a : I, x ⟶ i.obj (anchor a)) (fallback : ∀ y : B, x ⟶ y) (w : A) :
    overlapCoordinates i x index anchor q p fallback (i.obj w) =
      p (index w) ≫ i.map (q w) := by
  classical
  let h : ∃ z : A, i.obj z = i.obj w := ⟨w, rfl⟩
  have hz : Classical.choose h = w := hi (Classical.choose_spec h)
  simp only [overlapCoordinates, dite_eq_left h]
  have ht (a b : A) (hab : a = b) :
      (p (index a) ≫ i.map (q a)) ≫ eqToHom (congrArg i.obj hab) =
        p (index b) ≫ i.map (q b) := by
    cases hab
    simp
  simpa only [Category.assoc] using ht (Classical.choose h) w hz
/-- A connected left-hand groupoid and an overlap object embedding provide
normalized coordinates extending all prescribed overlap paths. The base vertex
is assumed outside the overlap, as in the standard cell-attachment cover. -/
theorem exists_overlapCoordinates
    {A B I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    (i : A ⥤ B) (hi : Function.Injective i.obj) (x : B)
    (hx : ∀ w : A, i.obj w ≠ x) (hB : ∀ y : B, Nonempty (x ⟶ y))
    (index : A → I) (anchor : I → A) (q : ∀ w : A, anchor (index w) ⟶ w)
    (p : ∀ a : I, x ⟶ i.obj (anchor a)) :
    ∃ s : ∀ y : B, x ⟶ y, s x = 𝟙 x ∧
      ∀ w : A, s (i.obj w) = p (index w) ≫ i.map (q w) := by
  classical
  refine ⟨overlapCoordinates i x index anchor q p (normalizedPaths x hB), ?_, ?_⟩
  · have hnot : ¬ ∃ w : A, i.obj w = x := by
      rintro ⟨w, hw⟩
      exact hx w hw
    simp [overlapCoordinates, hnot]
  · exact overlapCoordinates_on_overlap i hi x index anchor q p _
/-- Trivial vertex groups in a groupoid imply uniqueness of every morphism
between fixed endpoints; no connectedness between distinct components is needed. -/
theorem hom_subsingleton_of_end_subsingleton
    {C : Type u} [Groupoid.{u} C] (hC : ∀ y : C, Subsingleton (End y)) (x y : C) :
    Subsingleton (x ⟶ y) := by
  constructor
  intro f g
  have hfg : f ≫ inv g = 𝟙 x := (hC x).elim _ _
  have hh := congrArg (fun t : End x => t ≫ g) hfg
  simpa [Category.assoc] using hh
/-- Transporting a dependent family of paths along an equality of anchor
indices gives the other chosen path. -/
theorem dependent_path_congr
    {I C : Type u} [Category.{u} C] (anchor : I → C) (x : C)
    (p : ∀ a : I, x ⟶ anchor a) {a b : I} (h : a = b) :
    p a ≫ eqToHom (congrArg anchor h) = p b := by
  cases h
  simp
/-- Paths from a common vertex to each thin component's anchor, followed by
paths inside that component, give natural right-hand coordinates. -/
noncomputable def rightCoordinates
    {I C D : Type u} [Groupoid.{u} C] [Groupoid.{u} D]
    (l : C ⥤ D) (x : D) (index : C → I) (anchor : I → C)
    (s : ∀ y : C, anchor (index y) ⟶ y) (p : ∀ a : I, x ⟶ l.obj (anchor a)) :
    ∀ y : C, x ⟶ l.obj y := fun y => p (index y) ≫ l.map (s y)
theorem rightCoordinates_natural
    {I C D : Type u} [Groupoid.{u} C] [Groupoid.{u} D]
    (l : C ⥤ D) (x : D) (index : C → I) (anchor : I → C)
    (s : ∀ y : C, anchor (index y) ⟶ y) (p : ∀ a : I, x ⟶ l.obj (anchor a))
    (hC : ∀ y : C, Subsingleton (End y))
    (hindex : ∀ (y z : C) (_f : y ⟶ z), index y = index z)
    (y z : C) (f : y ⟶ z) :
    rightCoordinates l x index anchor s p y ≫ l.map f =
      rightCoordinates l x index anchor s p z := by
  have h := hindex y z f
  have hs : s y ≫ f = eqToHom (congrArg anchor h) ≫ s z :=
    (hom_subsingleton_of_end_subsingleton hC _ _).elim _ _
  change (p (index y) ≫ l.map (s y)) ≫ l.map f = p (index z) ≫ l.map (s z)
  rw [Category.assoc, ← l.map_comp, hs, l.map_comp, eqToHom_map l, ← Category.assoc]
  rw [dependent_path_congr (fun a => l.obj (anchor a)) x p h]
/-- An anchor path on the left becomes an anchor path for its right-hand
component by commutativity of the square. -/
noncomputable def mappedAnchorPaths
    {A B C D I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (hc : i ⋙ j = k ⋙ l) (x : B) (anchor : I → A)
    (p : ∀ a : I, x ⟶ i.obj (anchor a)) :
    ∀ a : I, j.obj x ⟶ l.obj (k.obj (anchor a)) :=
  fun a => j.map (p a) ≫ eqToHom (Functor.congr_obj hc (anchor a))
/-- The left and right anchor-coordinate constructions agree on the overlap.
Thinness of a right-hand component identifies the two paths from its anchor. -/
theorem rightCoordinates_match_overlap
    {A B C D I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (hc : i ⋙ j = k ⋙ l) (x : B) (indexA : A → I) (indexC : C → I)
    (anchor : I → A) (q : ∀ w : A, anchor (indexA w) ⟶ w)
    (p : ∀ a : I, x ⟶ i.obj (anchor a))
    (s : ∀ y : C, k.obj (anchor (indexC y)) ⟶ y)
    (hC : ∀ y : C, Subsingleton (End y))
    (hindex : ∀ w : A, indexC (k.obj w) = indexA w) (w : A) :
    HEq (j.map (p (indexA w) ≫ i.map (q w)))
      (rightCoordinates l (j.obj x) indexC (fun a => k.obj (anchor a)) s
        (mappedAnchorPaths i k j l hc x anchor p) (k.obj w)) := by
  let r := mappedAnchorPaths i k j l hc x anchor p
  have hi : indexA w = indexC (k.obj w) := (hindex w).symm
  have hs : k.map (q w) =
      eqToHom (congrArg (fun a => k.obj (anchor a)) hi) ≫ s (k.obj w) :=
    (hom_subsingleton_of_end_subsingleton hC _ _).elim _ _
  have hr : r (indexA w) ≫ l.map
      (eqToHom (congrArg (fun a => k.obj (anchor a)) hi)) = r (indexC (k.obj w)) := by
    rw [eqToHom_map]
    exact dependent_path_congr (fun a => l.obj (k.obj (anchor a))) (j.obj x) r hi
  apply (conj_eqToHom_iff_heq _ _ rfl (Functor.congr_obj hc w)).mp
  simp only [eqToHom_refl, Category.id_comp]
  change j.map (p (indexA w) ≫ i.map (q w)) =
    (r (indexC (k.obj w)) ≫ l.map (s (k.obj w))) ≫
      eqToHom (Functor.congr_obj hc w).symm
  calc
    j.map (p (indexA w) ≫ i.map (q w)) =
        r (indexA w) ≫ l.map (k.map (q w)) ≫
          eqToHom (Functor.congr_obj hc w).symm := by
      have hm := Functor.congr_hom hc (q w)
      change j.map (i.map (q w)) =
        eqToHom (Functor.congr_obj hc (anchor (indexA w))) ≫
          l.map (k.map (q w)) ≫ eqToHom (Functor.congr_obj hc w).symm at hm
      rw [j.map_comp, hm]
      simp [r, mappedAnchorPaths, Category.assoc]
    _ = (r (indexC (k.obj w)) ≫ l.map (s (k.obj w))) ≫
        eqToHom (Functor.congr_obj hc w).symm := by
      rw [hs, l.map_comp]
      simp only [← Category.assoc]
      rw [hr]
/-- Coordinates prescribed componentwise on the overlap kill every overlap
arrow as soon as they kill each component's transported cyclic generator. -/
theorem overlapCoordinates_eq_one_of_cyclic
    {A B I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    (i : A ⥤ B) (x : B) (index : A → I) (anchor : I → A)
    (q : ∀ w : A, anchor (index w) ⟶ w)
    (p : ∀ a : I, x ⟶ i.obj (anchor a)) (s : ∀ y : B, x ⟶ y)
    (hs : ∀ w : A, s (i.obj w) = p (index w) ≫ i.map (q w))
    (hindex : ∀ (y z : A) (_f : y ⟶ z), index y = index z)
    (r : ∀ a : I, End (anchor a))
    (hcyc : ∀ (a : I) (g : End (anchor a)), ∃ n : ℤ, g = r a ^ n)
    {G : Type u} [Group G] (F : End x →* G)
    (hr : ∀ a, F (overlapLoop i x (anchor a) (p a) (r a)) = 1)
    (y z : A) (f : y ⟶ z) :
    F (s (i.obj y) ≫ i.map f ≫ inv (s (i.obj z))) = 1 := by
  have h := hindex y z f
  let t : anchor (index y) ⟶ z := eqToHom (congrArg anchor h) ≫ q z
  have ht : p (index z) ≫ i.map (q z) = p (index y) ≫ i.map t := by
    dsimp [t]
    rw [i.map_comp, ← Category.assoc, eqToHom_map]
    rw [dependent_path_congr (fun a => i.obj (anchor a)) x p h]
  rw [hs y, hs z, ht]
  exact overlap_coordinate_eq_one_of_cyclic i x (anchor (index y)) y z
    (p (index y)) (q y) t f (r (index y)) (hcyc (index y)) F (hr (index y))
/-- The algebraic bridge from a categorical groupoid pushout to the quotient
of the actual left vertex group. Connectedness, overlap object embedding,
component paths, thin right-hand vertex groups, and cyclic overlap vertex groups
supply the path coordinates; neither surjectivity nor kernel exactness is assumed.
Applying this to a two-cell attachment still requires the genuine topological
open-cover pushout and proofs of all listed local groupoid hypotheses. -/
theorem pushout_vertex_quotient_of_component_data
    {A B C D I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (hi : Function.Injective i.obj) (x : B) (hx : ∀ w : A, i.obj w ≠ x)
    (hB : ∀ y : B, Nonempty (x ⟶ y))
    (indexA : A → I) (indexC : C → I) (anchor : I → A)
    (q : ∀ w : A, anchor (indexA w) ⟶ w)
    (p : ∀ a : I, x ⟶ i.obj (anchor a))
    (s : ∀ y : C, k.obj (anchor (indexC y)) ⟶ y)
    (hC : ∀ y : C, Subsingleton (End y))
    (hindexC : ∀ (y z : C) (_f : y ⟶ z), indexC y = indexC z)
    (hindex : ∀ w : A, indexC (k.obj w) = indexA w)
    (r : ∀ a : I, End (anchor a))
    (hcyc : ∀ (a : I) (g : End (anchor a)), ∃ n : ℤ, g = r a ^ n) :
    let R : I → End x := fun a => overlapLoop i x (anchor a) (p a) (r a)
    Function.Surjective (j.mapEnd x) ∧
      (j.mapEnd x).ker = Subgroup.normalClosure (Set.range R) ∧
      ∃ E : End x ⧸ Subgroup.normalClosure (Set.range R) ≃* End (j.obj x),
        ∀ g : End x, E (QuotientGroup.mk' (Subgroup.normalClosure (Set.range R)) g) =
          j.mapEnd x g := by
  intro R
  have hc : i ⋙ j = k ⋙ l := congrArg Cat.Hom.toFunctor h.w
  obtain ⟨pB, hpB, hpres⟩ := exists_overlapCoordinates i hi x hx hB indexA anchor q p
  let c := rightCoordinates l (j.obj x) indexC (fun a => k.obj (anchor a)) s
    (mappedAnchorPaths i k j l hc x anchor p)
  have hn : ∀ (y z : C) (f : y ⟶ z), c y ≫ l.map f = c z :=
    rightCoordinates_natural l (j.obj x) indexC (fun a => k.obj (anchor a)) s
      (mappedAnchorPaths i k j l hc x anchor p) hC hindexC
  have hw : ∀ w : A, HEq (j.map (pB (i.obj w))) (c (k.obj w)) := by
    intro w
    rw [hpres w]
    exact rightCoordinates_match_overlap i k j l hc x indexA indexC anchor q p s hC hindex w
  have hindexA : ∀ (y z : A) (_f : y ⟶ z), indexA y = indexA z := by
    intro y z f
    exact (hindex y).symm.trans ((hindexC _ _ (k.map f)).trans (hindex z))
  have hr : ∀ a, j.mapEnd x (R a) = 1 := by
    intro a
    apply map_overlapLoop_eq_one i k j l hc x (anchor a) (p a) (r a)
    exact (hC (k.obj (anchor a))).elim _ _
  have hoverlap : ∀ (y z : A) (f : y ⟶ z),
      QuotientGroup.mk' (Subgroup.normalClosure (Set.range R))
        (pB (i.obj y) ≫ i.map f ≫ inv (pB (i.obj z))) = 1 := by
    apply overlapCoordinates_eq_one_of_cyclic i x indexA anchor q p pB hpres hindexA r hcyc
    intro a
    change (R a : End x ⧸ Subgroup.normalClosure (Set.range R)) = 1
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.subset_normalClosure (Set.mem_range_self a))
  obtain ⟨hsurj, hker⟩ := pushout_exact_of_path_coordinates i k j l h x pB hpB R hr
    hoverlap c hn hw
  exact ⟨hsurj, hker,
    quotientNormalClosureEquiv R (j.mapEnd x) hsurj hker, fun _ => rfl⟩
end ArrowDescent
end CellAttachment
end CellAttachment_GroupoidQuotient
/-! Source module: CellAttachment.Adjunction -/
section CellAttachment_Adjunction
/-!
# Genuine adjunction space for an arbitrary family of two-cells
The carrier is the quotient of the topological disjoint union of the original
space and the indexed closed complex unit disks. The relation is generated by
exactly the prescribed boundary identifications; the topology is the quotient
topology. No separation or finiteness assumptions are used.
-/
noncomputable section
namespace CellAttachment
universe u v
/-- The closed two-dimensional unit disk in the complex plane. -/
abbrev Disk := {z : ℂ // ‖z‖ ≤ 1}
/-- The inclusion of the unit circle into the closed disk. -/
def boundaryInclusion : C(Circle, Disk) where
  toFun z := ⟨z, le_of_eq (Circle.norm_coe z)⟩
  continuous_toFun := by fun_prop
/-- The actual topological disjoint union before attaching the disks. -/
abbrev Raw (X : Type u) (ι : Type v) := X ⊕ (Σ _ : ι, Disk)
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
/-- Only boundary points are identified with their prescribed attaching images. -/
inductive AttachingRel (f : ι → C(Circle, X)) : Raw X ι → Raw X ι → Prop
  | boundary (i : ι) (z : Circle) :
      AttachingRel f (.inr ⟨i, boundaryInclusion z⟩) (.inl (f i z))
/-- The adjunction quotient, with its induced quotient topology. -/
def Space (f : ι → C(Circle, X)) := Quot (AttachingRel f)
instance (f : ι → C(Circle, X)) : TopologicalSpace (Space f) :=
  inferInstanceAs (TopologicalSpace (Quot (AttachingRel f)))
/-- The quotient map from the unglued topological disjoint union. -/
def quotientMap (f : ι → C(Circle, X)) : C(Raw X ι, Space f) :=
  ⟨Quot.mk _, continuous_quot_mk⟩
/-- The actual continuous inclusion of the original space. -/
def inclusion (f : ι → C(Circle, X)) : C(X, Space f) where
  toFun x := quotientMap f (.inl x)
  continuous_toFun := (quotientMap f).continuous.comp continuous_inl
/-- The characteristic map of an attached closed disk. -/
def characteristic (f : ι → C(Circle, X)) (i : ι) : C(Disk, Space f) where
  toFun z := quotientMap f (.inr ⟨i, z⟩)
  continuous_toFun := (quotientMap f).continuous.comp
    (continuous_inr.comp (continuous_sigmaMk (i := i)))
@[simp] theorem characteristic_boundary (f : ι → C(Circle, X)) (i : ι) (z : Circle) :
    characteristic f i (boundaryInclusion z) = inclusion f (f i z) :=
  Quot.sound (.boundary i z)
/-- The quotient map is a quotient map, not merely a continuous surjection. -/
theorem quotientMap_isQuotientMap (f : ι → C(Circle, X)) :
    Topology.IsQuotientMap (quotientMap f) := isQuotientMap_quot_mk
/-- Identify the boundary point of a disk with a circle point. -/
def diskBoundaryPoint (z : Disk) (h : ‖(z : ℂ)‖ = 1) : Circle :=
  ⟨z, mem_sphere_zero_iff_norm.mpr h⟩
/-- An algebraic invariant used only to distinguish points of the original space.
It is deliberately not asserted to be continuous. -/
def baseValue (f : ι → C(Circle, X)) : Raw X ι → Option X
  | .inl x => some x
  | .inr ⟨i, z⟩ => if h : ‖(z : ℂ)‖ = 1 then some (f i (diskBoundaryPoint z h)) else none
theorem baseValue_respects (f : ι → C(Circle, X)) {a b : Raw X ι}
    (h : AttachingRel f a b) : baseValue f a = baseValue f b := by
  cases h with
  | boundary i z =>
    change (if h : ‖(z : ℂ)‖ = 1 then some (f i (diskBoundaryPoint (boundaryInclusion z) h)) else none) = some (f i z)
    rw [dite_eq_left (Circle.norm_coe z)]
    rfl
/-- Algebraic readout of the base value descends through precisely the attaching relation. -/
def quotientBaseValue (f : ι → C(Circle, X)) : Space f → Option X :=
  Quot.lift (baseValue f) (fun _ _ h => baseValue_respects f h)
/-- The attaching quotient never identifies two distinct original points. -/
theorem inclusion_injective (f : ι → C(Circle, X)) : Function.Injective (inclusion f) := by
  intro x y h
  have h' := congrArg (quotientBaseValue f) h
  exact Option.some.inj h'
/-- The specified map on fundamental groups is induced by the actual inclusion. -/
def inclusionPi1 (f : ι → C(Circle, X)) (x₀ : X) :
    FundamentalGroup X x₀ →* FundamentalGroup (Space f) (inclusion f x₀) :=
  FundamentalGroup.map (inclusion f) x₀
end CellAttachment
end
end CellAttachment_Adjunction
/-! Source module: CellAttachment.NormalForm -/
section CellAttachment_NormalForm
/-!
# Algebraic normal forms in the genuine attaching quotient
These normal forms classify quotient points. They do not replace the quotient
topology by a disjoint-union topology and are not asserted to be continuous.
-/
noncomputable section
namespace CellAttachment
universe u v
abbrev OpenDisk := {z : ℂ // ‖z‖ < 1}
abbrev NormalForm (X : Type u) (ι : Type v) := X ⊕ (Σ _ : ι, OpenDisk)
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
/-- The representative of an interior disk point in the raw disjoint union. -/
def interiorRepresentative (i : ι) (z : OpenDisk) : Raw X ι :=
  .inr ⟨i, ⟨z, z.property.le⟩⟩
/-- Interior points remain points of their unique disk; boundary points go to X. -/
def normalize (f : ι → C(Circle, X)) : Raw X ι → NormalForm X ι
  | .inl x => .inl x
  | .inr ⟨i, z⟩ =>
      if h : ‖(z : ℂ)‖ = 1 then .inl (f i (diskBoundaryPoint z h))
      else .inr ⟨i, ⟨z, lt_of_le_of_ne z.property h⟩⟩
theorem normalize_respects (f : ι → C(Circle, X)) {a b : Raw X ι}
    (h : AttachingRel f a b) : normalize f a = normalize f b := by
  cases h with
  | boundary i z =>
    change (if h : ‖(z : ℂ)‖ = 1 then (Sum.inl (f i (diskBoundaryPoint (boundaryInclusion z) h)) : NormalForm X ι)
      else Sum.inr ⟨i, _⟩) = Sum.inl (f i z)
    rw [dite_eq_left (Circle.norm_coe z)]
    rfl
/-- A well-defined algebraic normal form for every quotient point. -/
def normalForm (f : ι → C(Circle, X)) : Space f → NormalForm X ι :=
  Quot.lift (normalize f) (fun _ _ h => normalize_respects f h)
/-- Pick the raw representative of a normal form. -/
def normalRepresentative : NormalForm X ι → Raw X ι
  | .inl x => .inl x
  | .inr ⟨i, z⟩ => interiorRepresentative i z
@[simp] theorem normalize_normalRepresentative (f : ι → C(Circle, X))
    (n : NormalForm X ι) : normalize f (normalRepresentative n) = n := by
  cases n with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i, z⟩
    change (if h : ‖(z : ℂ)‖ = 1 then _ else _) = _
    rw [dite_eq_right (ne_of_lt z.property)]
/-- Normalization changes a representative only by prescribed boundary gluings. -/
theorem quotient_normalRepresentative_normalize (f : ι → C(Circle, X)) (a : Raw X ι) :
    quotientMap f (normalRepresentative (normalize f a)) = quotientMap f a := by
  cases a with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i, z⟩
    by_cases h : ‖(z : ℂ)‖ = 1
    · simp only [normalize, h, dite_true, normalRepresentative]
      exact (Quot.sound (.boundary i (diskBoundaryPoint z h))).symm
    · simp only [normalize, h, dite_false, normalRepresentative, interiorRepresentative]
/-- Equality in the adjunction quotient is exactly equality of the algebraic normal forms. -/
theorem quotient_eq_iff_normalize_eq (f : ι → C(Circle, X)) (a b : Raw X ι) :
    quotientMap f a = quotientMap f b ↔ normalize f a = normalize f b := by
  constructor
  · exact fun h => congrArg (normalForm f) h
  · intro h
    rw [← quotient_normalRepresentative_normalize f a,
      ← quotient_normalRepresentative_normalize f b, h]
/-- Every interior point has its own unchanged normal form. -/
@[simp] theorem normalForm_interiorRepresentative (f : ι → C(Circle, X)) (i : ι) (z : OpenDisk) :
    normalForm f (quotientMap f (interiorRepresentative i z)) = .inr ⟨i, z⟩ :=
  normalize_normalRepresentative f (.inr ⟨i, z⟩)
@[simp] theorem normalForm_inclusion (f : ι → C(Circle, X)) (x : X) :
    normalForm f (inclusion f x) = .inl x := rfl
/-- All disk interiors embed algebraically as a disjoint family. -/
theorem interiors_injective (f : ι → C(Circle, X)) :
    Function.Injective (fun z : Σ _ : ι, OpenDisk =>
      quotientMap f (interiorRepresentative z.1 z.2)) := by
  intro a b h
  have h' := congrArg (normalForm f) h
  simpa using h'
/-- No interior point is identified with an original point. -/
theorem interior_ne_inclusion (f : ι → C(Circle, X)) (i : ι) (z : OpenDisk) (x : X) :
    quotientMap f (interiorRepresentative i z) ≠ inclusion f x := by
  intro h
  have h' := congrArg (normalForm f) h
  simpa using h'
end CellAttachment
end
end CellAttachment_NormalForm
/-! Source module: CellAttachment.CircleGenerator -/
section CellAttachment_CircleGenerator
/-
Copyright (c) 2026 Ruize Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruize Chen
This is a local backport from mathlib commit
389347a7c1cfa76f6bd5be2ca35d4cb621610ad3, file
Mathlib/Topology/Covering/FundamentalGroupCircle.lean (Apache 2.0):
https://github.com/leanprover-community/mathlib4/blob/389347a7c1cfa76f6bd5be2ca35d4cb621610ad3/Mathlib/Topology/Covering/FundamentalGroupCircle.lean
The supporting lifting lemmas below are backported from the same commit's
Mathlib/Topology/Homotopy/Lifting.lean, copyright (c) 2025 Junyan Xu.
https://github.com/leanprover-community/mathlib4/blob/389347a7c1cfa76f6bd5be2ca35d4cb621610ad3/Mathlib/Topology/Homotopy/Lifting.lean
The zmultiples equivalence is adapted, specialized to real numbers, from
Mathlib/Algebra/Group/Subgroup/ZPowers/Lemmas.lean, copyright (c) 2020
Chris Hughes, authors Chris Hughes and Snir Broshi (Apache 2.0).
https://github.com/leanprover-community/mathlib4/blob/389347a7c1cfa76f6bd5be2ca35d4cb621610ad3/Mathlib/Algebra/Group/Subgroup/ZPowers/Lemmas.lean
All additions after `end AddCircle` are project-specific.
-/
/-!
# The fundamental group of the circle
For `0 < p`, the fundamental group of `AddCircle p` at any basepoint is isomorphic to `ℤ`
(`AddCircle.windingNumberIso`). The winding number `AddCircle.windingNumber` of a loop is
`(f 1 - f 0) / p` for any continuous lift `f : I → ℝ` of the loop
(`AddCircle.windingNumber_eq_div`); in particular the loop `t ↦ n • (t * p) + x` has winding
number `n` (`AddCircle.windingNumber_zsmulLoop`).
-/
open unitInterval
noncomputable section
namespace AddSubgroup
/-- Backported real specialization of the integer-multiples equivalence. -/
def zmultiplesEquivInt {a : ℝ} (ha : a ≠ 0) : zmultiples a ≃+ ℤ :=
  ((AddMonoidHom.ofInjective (show Function.Injective (zmultiplesHom ℝ a) from
    smul_left_injective ℤ ha)).trans
    (AddEquiv.addSubgroupCongr (range_zmultiplesHom a))).symm
@[simp]
theorem coe_zmultiplesEquivInt_symm_apply {a : ℝ} (ha : a ≠ 0) (n : ℤ) :
    ((zmultiplesEquivInt ha).symm n : ℝ) = n • a := by
  simp only [zmultiplesEquivInt, AddEquiv.symm_symm, AddEquiv.trans_apply,
    AddEquiv.addSubgroupCongr_apply, AddMonoidHom.ofInjective_apply, zmultiplesHom_apply]
@[simp]
theorem zmultiplesEquivInt_apply_zsmul {a : ℝ} (ha : a ≠ 0) (n : ℤ) :
    zmultiplesEquivInt ha ⟨n • a, zsmul_mem_zmultiples a n⟩ = n :=
  (zmultiplesEquivInt ha).eq_symm_apply.mp (Subtype.ext (by simp))
end AddSubgroup
namespace IsCoveringMap
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (cov : IsCoveringMap p)
theorem coe_monodromy_mk {x y : X} (γ : Path x y) (e : p ⁻¹' {x}) :
    (cov.monodromy (.mk γ) e : E) = cov.liftPath γ e (γ.source.trans e.2.symm) 1 :=
  rfl
lemma monodromy_eq_apply_one {x y : X} {γ : Path x y} {e : p ⁻¹' {x}} {Γ : C(I, E)}
    (hpΓ : p ∘ Γ = γ) (Γ_0 : Γ 0 = e) : cov.monodromy (.mk γ) e = Γ 1 := by
  rw [show Γ = cov.liftPath γ e (γ.source.trans e.2.symm) from
    (eq_liftPath_iff' ..).mpr ⟨hpΓ, Γ_0⟩, coe_monodromy_mk]
end IsCoveringMap
namespace IsQuotientCoveringMap
variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)
  {x : X} (e : p ⁻¹' {x}) {γ : FundamentalGroup X x} {g : G}
theorem fundamentalGroupToMulOpposite_apply_mk_eq {e : p ⁻¹' {x}}
    {γ : Path x x} {g : G} {Γ : C(I, E)}
    (hpΓ : p ∘ Γ = γ) (Γ_0 : Γ 0 = e) (Γ_1 : Γ 1 = g • e) :
    hp.fundamentalGroupToMulOpposite e (.mk γ) = .op g :=
  hp.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr <| by
    simp [hp.isCoveringMap.monodromy_eq_apply_one hpΓ Γ_0, Γ_1]
theorem fundamentalGroupToMulOpposite_toPermFiber :
    hp.fundamentalGroupToMulOpposite (hp.toPermFiber x g e) γ =
      MulOpposite.op (g * (hp.fundamentalGroupToMulOpposite e γ).unop * g⁻¹) := by
  rw [fundamentalGroupToMulOpposite_apply_eq_Iff, hp.monodromy_toPermFiber]
  simp only [MulOpposite.unop_op, toPermFiber_apply_apply_coe,
    ← hp.unop_fundamentalGroupToMulOpposite_smul, mul_smul, inv_smul_smul]
theorem fundamentalGroupToMulOpposite_eq [IsMulCommutative G] (e' : p ⁻¹' {x}) :
    hp.fundamentalGroupToMulOpposite e = hp.fundamentalGroupToMulOpposite e' := by
  obtain ⟨g, rfl⟩ := hp.exists_toPermFiber_eq e e'
  ext γ
  rw [fundamentalGroupToMulOpposite_toPermFiber, mul_comm' g, mul_inv_cancel_right,
    MulOpposite.op_unop]
theorem fundamentalGroupEquiv_eq [SimplyConnectedSpace E] [IsMulCommutative G]
    (e' : p ⁻¹' {x}) : hp.fundamentalGroupEquiv e = hp.fundamentalGroupEquiv e' :=
  MulEquiv.ext fun γ ↦ congr($(hp.fundamentalGroupToMulOpposite_eq e e') γ)
end IsQuotientCoveringMap
namespace IsAddQuotientCoveringMap
variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [AddGroup G] [AddAction G E] {p : E → X} (hp : IsAddQuotientCoveringMap p G)
  {x : X} (e : p ⁻¹' {x})
theorem fundamentalGroupToMulOpposite_apply_mk_eq {e : p ⁻¹' {x}}
    {γ : Path x x} {g : Multiplicative G}
    {Γ : C(I, E)} (hpΓ : p ∘ Γ = γ) (Γ_0 : Γ 0 = e) (Γ_1 : Γ 1 = g • e) :
    hp.fundamentalGroupToMulOpposite e (.mk γ) = .op g :=
  hp.toMultiplicative.fundamentalGroupToMulOpposite_apply_mk_eq hpΓ Γ_0 Γ_1
theorem fundamentalGroupEquiv_eq [SimplyConnectedSpace E] [IsAddCommutative G]
    (e' : p ⁻¹' {x}) : hp.fundamentalGroupEquiv e = hp.fundamentalGroupEquiv e' := by
  let : IsMulCommutative (Multiplicative G) := ⟨⟨fun a b =>
    congrArg Multiplicative.ofAdd (add_comm' a.toAdd b.toAdd)⟩⟩
  exact
  hp.toMultiplicative.fundamentalGroupEquiv_eq e e'
end IsAddQuotientCoveringMap
namespace AddCircle
variable (p : ℝ)
/-- The loop in `AddCircle p` based at `x` that winds `n` times, defined as
`t ↦ n • (t * p) + x`. -/
def zsmulLoop (x : ℝ) (n : ℤ) : Path (x : AddCircle p) x where
  toFun t := n • (t * p : ℝ) + x
  source' := by simp
  target' := by simp [coe_period]
  continuous_toFun := by fun_prop
@[simp]
theorem zsmulLoop_apply (x : ℝ) (n : ℤ) (t : I) :
    zsmulLoop p x n t = n • (t * p : ℝ) + x :=
  rfl
variable {p} [hp : Fact (0 < p)]
/-- **The fundamental group of the circle is `ℤ`**: the isomorphism sends the class of a loop to
its winding number (`windingNumber_eq_div`). It does not depend on the choice of a lift of the
basepoint (`IsAddQuotientCoveringMap.fundamentalGroupEquiv_eq`). -/
noncomputable def windingNumberIso (x : AddCircle p) :
    FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ :=
  ((isAddQuotientCoveringMap_coe p).fundamentalGroupEquiv (x := x)
      ⟨(equivIco p 0 x : ℝ), coe_equivIco⟩).trans <|
    MulOpposite.opMulEquiv.symm.trans (AddSubgroup.zmultiplesEquivInt hp.out.ne').toMultiplicative
/-- The winding number of a loop in `AddCircle p`, defined as its image under `windingNumberIso`. -/
noncomputable def windingNumber {x : AddCircle p} (γ : FundamentalGroup (AddCircle p) x) : ℤ :=
  (windingNumberIso x γ).toAdd
/-- The winding number of a loop in `AddCircle p` is `(f 1 - f 0) / p`, for any continuous lift
`f` of the loop to `ℝ`. -/
theorem windingNumber_eq_div {x : AddCircle p} (γ : Path x x) (f : C(I, ℝ)) (hf : (↑) ∘ f = γ) :
    (windingNumber (.mk γ) : ℝ) = (f 1 - f 0) / p := by
  have h0 : (f 0 : AddCircle p) = x := congr($hf 0).trans γ.source
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n • p = f 1 - f 0 :=
    AddSubgroup.mem_zmultiples_iff.mp <| QuotientAddGroup.eq_iff_sub_mem.mp <|
      congr($hf 1).trans <| γ.target.trans h0.symm
  have h : (isAddQuotientCoveringMap_coe p).fundamentalGroupEquiv (x := x) ⟨f 0, h0⟩ (.mk γ) =
      .op (.ofAdd ⟨n • p, n, rfl⟩) :=
    (isAddQuotientCoveringMap_coe p).fundamentalGroupToMulOpposite_apply_mk_eq hf rfl (by simp [hn])
  simp [windingNumber, windingNumberIso, AddSubgroup.zmultiplesEquivInt_apply_zsmul hp.out.ne' n,
    (isAddQuotientCoveringMap_coe p).fundamentalGroupEquiv_eq _ ⟨f 0, h0⟩, h,
    eq_div_iff hp.out.ne', ← zsmul_eq_mul, ← hn]
/-- The loop `t ↦ n • (t * p) + x` has winding number `n`. -/
theorem windingNumber_zsmulLoop (x : ℝ) (n : ℤ) :
    windingNumber (x := x) (.mk (zsmulLoop p x n)) = n := by
  simpa [hp.out.ne'] using windingNumber_eq_div (zsmulLoop p x n)
    ⟨fun t ↦ n • (t * p) + x, by fun_prop⟩ rfl
end AddCircle
/-! ## Project-specific concrete circle generator -/
namespace CellAttachment
/-- The standard positively oriented circle loop, `t ↦ exp(2πt)`, based at `1`. -/
def circleGenerator : Path (1 : Circle) 1 where
  toFun t := Circle.exp ((t : ℝ) * (2 * Real.pi))
  source' := by simp
  target' := by simp
  continuous_toFun := by fun_prop
@[simp]
theorem circleGenerator_apply (t : I) :
    circleGenerator t = Circle.exp ((t : ℝ) * (2 * Real.pi)) := rfl
/-- The corresponding homotopy class in the actual fundamental group. -/
def circleGeneratorClass : FundamentalGroup Circle (1 : Circle) :=
  .mk circleGenerator
/-- The complex unit circle fundamental group, identified with the integers by lifting
through the real exponential covering. -/
def circleFundamentalGroupEquivInt :
    FundamentalGroup Circle (1 : Circle) ≃* Multiplicative ℤ :=
  (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
    ⟨0, Circle.exp_zero⟩).trans <|
    MulOpposite.opMulEquiv.symm.trans
      (AddSubgroup.zmultiplesEquivInt (by positivity : (2 * Real.pi : ℝ) ≠ 0)).toMultiplicative
@[simp]
theorem circleFundamentalGroupEquivInt_generator :
    circleFundamentalGroupEquivInt circleGeneratorClass = Multiplicative.ofAdd (1 : ℤ) := by
  have h : Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
      ⟨0, Circle.exp_zero⟩ circleGeneratorClass =
        .op (.ofAdd ⟨(1 : ℤ) • (2 * Real.pi), 1, rfl⟩) := by
    exact Circle.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite_apply_mk_eq
      (Γ := ⟨fun t => (t : ℝ) * (2 * Real.pi), by fun_prop⟩) rfl (by simp) (by simp)
  change Multiplicative.ofAdd
    (AddSubgroup.zmultiplesEquivInt (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (MulOpposite.unop
        (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
          ⟨0, Circle.exp_zero⟩ circleGeneratorClass)).toAdd) = _
  rw [h]
  exact congrArg Multiplicative.ofAdd (AddSubgroup.zmultiplesEquivInt_apply_zsmul
    (by positivity : (2 * Real.pi : ℝ) ≠ 0) 1)
/-- Every actual based homotopy class on the complex unit circle is an integer power of
the standard loop. This is the generator fact needed for attaching two-cells. -/
theorem circleGenerator_generates (γ : FundamentalGroup Circle (1 : Circle)) :
    ∃ n : ℤ, circleGeneratorClass ^ n = γ := by
  refine ⟨(circleFundamentalGroupEquivInt γ).toAdd, ?_⟩
  apply circleFundamentalGroupEquivInt.injective
  rw [map_zpow, circleFundamentalGroupEquivInt_generator]
  change (circleFundamentalGroupEquivInt γ).toAdd • (1 : ℤ) =
    (circleFundamentalGroupEquivInt γ).toAdd
  simp
/-- The cyclic subgroup generated by the standard circle loop is the whole fundamental group. -/
theorem circleGenerator_zpowers_eq_top :
    Subgroup.zpowers circleGeneratorClass = ⊤ := by
  apply top_unique
  intro γ _
  exact circleGenerator_generates γ
/-- `AddCircle (2π)` and the complex unit circle are the same circle model. -/
def additiveCircleIdentification : AddCircle (2 * Real.pi) ≃ₜ Circle :=
  AddCircle.homeomorphCircle'
@[simp]
theorem additiveCircleIdentification_zero :
    additiveCircleIdentification (0 : AddCircle (2 * Real.pi)) = (1 : Circle) := by
  change Circle.exp 0 = 1
  simp
/-- Mapping the additive generator through the standard homeomorphism gives precisely
the standard complex-circle loop, with its basepoints explicitly identified. -/
theorem additiveCircle_generator_identification :
    ((AddCircle.zsmulLoop (2 * Real.pi) 0 1).map
      additiveCircleIdentification.continuous).cast
        additiveCircleIdentification_zero.symm additiveCircleIdentification_zero.symm =
      circleGenerator := by
  apply Path.ext
  funext t
  change AddCircle.homeomorphCircle'
    ((1 : ℤ) • ((t : ℝ) * (2 * Real.pi)) + (0 : ℝ) : ℝ) =
      Circle.exp ((t : ℝ) * (2 * Real.pi))
  simp [AddCircle.homeomorphCircle'_apply_mk]
end CellAttachment
end
end CellAttachment_CircleGenerator
/-! Source module: CellAttachment.Annulus -/
section CellAttachment_Annulus
/-! # Genuine open-disk and punctured-open-disk geometry
The punctured open disk retracts to the circle at radius `1/2`, which lies inside
its domain. Normalizing to the radius-one boundary alone would not give a
self-map of the open disk.
-/
noncomputable section
open scoped unitInterval ContinuousMap
namespace CellAttachment
/-- The annular intersection model is the genuine punctured open unit disk. -/
abbrev Annulus := {z : OpenDisk // (z : ℂ) ≠ 0}
/-- The actual complex coordinate on the punctured open disk. -/
def annulusCoordinate : C(Annulus, ℂ) :=
  ⟨fun z => z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩
lemma annulus_norm_pos (z : Annulus) : 0 < ‖annulusCoordinate z‖ :=
  norm_pos_iff.mpr z.property
lemma annulus_norm_lt_one (z : Annulus) : ‖annulusCoordinate z‖ < 1 :=
  z.1.property
/-- Polar normalization into the actual complex unit circle. -/
def annulusPolar : C(Annulus, Circle) where
  toFun z := ⟨(‖annulusCoordinate z‖⁻¹ : ℝ) • annulusCoordinate z, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀]
    exact ne_of_gt (annulus_norm_pos z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((annulusCoordinate.continuous.norm.inv₀
      (fun z => ne_of_gt (annulus_norm_pos z))).smul annulusCoordinate.continuous)
/-- The radius-half circle lies inside the punctured open disk. -/
def halfCircle : C(Circle, Annulus) where
  toFun z := ⟨⟨(1 / 2 : ℝ) • (z : ℂ), by
    rw [norm_smul, Real.norm_eq_abs, Circle.norm_coe]
    norm_num⟩, smul_ne_zero (by norm_num) (Circle.coe_ne_zero z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_const : Continuous fun _ : Circle => (1 / 2 : ℝ)).smul
      (continuous_subtype_val : Continuous fun z : Circle => (z : ℂ))
@[simp] lemma annulusCoordinate_halfCircle (z : Circle) :
    annulusCoordinate (halfCircle z) = (1 / 2 : ℝ) • (z : ℂ) := rfl
@[simp] lemma annulus_norm_halfCircle (z : Circle) :
    ‖annulusCoordinate (halfCircle z)‖ = (1 / 2 : ℝ) := by
  rw [annulusCoordinate_halfCircle, norm_smul, Real.norm_eq_abs, Circle.norm_coe]
  norm_num
@[simp] lemma annulusPolar_halfCircle (z : Circle) : annulusPolar (halfCircle z) = z := by
  apply Subtype.ext
  change ‖annulusCoordinate (halfCircle z)‖⁻¹ • ((1 / 2 : ℝ) • (z : ℂ)) = _
  rw [annulus_norm_halfCircle, smul_smul]
  norm_num
/-- The coefficient interpolating the original radius and radius one half. -/
def annulusRadialCoefficient (t : unitInterval) (z : Annulus) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) * (1 / 2) * ‖annulusCoordinate z‖⁻¹
lemma annulusRadialCoefficient_mul_norm (t : unitInterval) (z : Annulus) :
    annulusRadialCoefficient t z * ‖annulusCoordinate z‖ =
      (1 - (t : ℝ)) * ‖annulusCoordinate z‖ + (t : ℝ) * (1 / 2) := by
  unfold annulusRadialCoefficient
  rw [add_mul, mul_assoc, inv_mul_cancel₀ (ne_of_gt (annulus_norm_pos z)), mul_one]
lemma annulusRadialCoefficient_pos (t : unitInterval) (z : Annulus) :
    0 < annulusRadialCoefficient t z := by
  have hi : 0 < ‖annulusCoordinate z‖⁻¹ := inv_pos.mpr (annulus_norm_pos z)
  have ht0 := t.property.1
  have ht1 := t.property.2
  unfold annulusRadialCoefficient
  by_cases h : (t : ℝ) = 1
  · rw [h]
    positivity
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne ht1 h
    have hnonneg : 0 ≤ (t : ℝ) * (1 / 2) * ‖annulusCoordinate z‖⁻¹ := by positivity
    linarith
lemma annulusRadialCoefficient_mul_norm_lt_one (t : unitInterval) (z : Annulus) :
    annulusRadialCoefficient t z * ‖annulusCoordinate z‖ < 1 := by
  rw [annulusRadialCoefficient_mul_norm]
  have ht0 := t.property.1
  have ht1 := t.property.2
  by_cases h : (t : ℝ) = 1
  · rw [h]
    norm_num
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne ht1 h
    have hm := mul_lt_mul_of_pos_left (annulus_norm_lt_one z) (by linarith : 0 < 1 - (t : ℝ))
    nlinarith
/-- Explicit radial deformation within the actual punctured open disk. -/
def annulusRadialDeformation (t : unitInterval) (z : Annulus) : Annulus :=
  ⟨⟨annulusRadialCoefficient t z • annulusCoordinate z, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (annulusRadialCoefficient_pos t z)]
      exact annulusRadialCoefficient_mul_norm_lt_one t z⟩,
    smul_ne_zero (ne_of_gt (annulusRadialCoefficient_pos t z)) z.property⟩
lemma annulusRadialDeformation_continuous :
    Continuous (fun p : unitInterval × Annulus => annulusRadialDeformation p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous ((fun p : unitInterval × Annulus => annulusRadialCoefficient p.1 p.2) •
    (fun p : unitInterval × Annulus => annulusCoordinate p.2))
  apply Continuous.smul
  · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
        ((annulusCoordinate.continuous.comp continuous_snd).norm.inv₀
          (fun p => ne_of_gt (annulus_norm_pos p.2))))
  · exact annulusCoordinate.continuous.comp continuous_snd
@[simp] lemma annulusRadialDeformation_zero (z : Annulus) :
    annulusRadialDeformation 0 z = z := by
  apply Subtype.ext
  apply Subtype.ext
  simp [annulusRadialDeformation, annulusRadialCoefficient, annulusCoordinate]
@[simp] lemma annulusRadialDeformation_one (z : Annulus) :
    annulusRadialDeformation 1 z = halfCircle (annulusPolar z) := by
  apply Subtype.ext
  apply Subtype.ext
  change annulusRadialCoefficient 1 z • annulusCoordinate z =
    (1 / 2 : ℝ) • (‖annulusCoordinate z‖⁻¹ • annulusCoordinate z)
  simp [annulusRadialCoefficient, mul_assoc]
/-- The radius-half circle is fixed throughout the deformation. -/
lemma annulusRadialDeformation_halfCircle (t : unitInterval) (z : Circle) :
    annulusRadialDeformation t (halfCircle z) = halfCircle z := by
  apply Subtype.ext
  apply Subtype.ext
  change annulusRadialCoefficient t (halfCircle z) • annulusCoordinate (halfCircle z) =
    annulusCoordinate (halfCircle z)
  have hc : annulusRadialCoefficient t (halfCircle z) = 1 := by
    unfold annulusRadialCoefficient
    rw [annulus_norm_halfCircle]
    ring
  rw [hc, one_smul]
/-- The explicit homotopy from the identity to the half-radius polar projection. -/
def annulusRadialHomotopy :
    (ContinuousMap.id Annulus).Homotopy (halfCircle.comp annulusPolar) where
  toFun p := annulusRadialDeformation p.1 p.2
  continuous_toFun := annulusRadialDeformation_continuous
  map_zero_left := annulusRadialDeformation_zero
  map_one_left := annulusRadialDeformation_one
/-- Polar projection and the half-radius embedding give a genuine homotopy equivalence. -/
def annulusHomotopyEquivCircle : Annulus ≃ₕ Circle where
  toFun := annulusPolar
  invFun := halfCircle
  left_inv := ⟨annulusRadialHomotopy.symm⟩
  right_inv := by
    have h : annulusPolar.comp halfCircle = ContinuousMap.id Circle := by
      apply ContinuousMap.ext
      exact annulusPolar_halfCircle
    rw [h]
/-- Path-connectedness transfers along the explicit homotopy equivalence. -/
theorem homotopyEquivPathConnectedSpace {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace Y] (e : X ≃ₕ Y) :
    PathConnectedSpace X where
  nonempty := ⟨e.invFun (Classical.arbitrary Y)⟩
  joined x y := ⟨((e.left_inv.some.evalAt x).symm.trans
    ((PathConnectedSpace.somePath (e x) (e y)).map e.invFun.continuous)).trans
      (e.left_inv.some.evalAt y)⟩
/-- The annulus is path connected by radial paths and paths on the radius-half circle. -/
instance annulus_pathConnectedSpace : PathConnectedSpace Annulus :=
  homotopyEquivPathConnectedSpace annulusHomotopyEquivCircle
/-- A homotopy equivalence induces the actual map on based fundamental groups
as a multiplicative equivalence. Its forward map is not an abstract choice. -/
def homotopyEquivFundamentalGroup {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) : FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x)
@[simp] lemma homotopyEquivFundamentalGroup_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (x : X)
    (γ : FundamentalGroup X x) :
    homotopyEquivFundamentalGroup e x γ = FundamentalGroup.map e.toFun x γ := rfl
/-- The based version with the target basepoint explicitly identified. -/
def homotopyEquivFundamentalGroupOfEq {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) {x : X} {y : Y} (h : e x = y) :
    FundamentalGroup X x ≃* FundamentalGroup Y y :=
  (homotopyEquivFundamentalGroup e x).trans
    (CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk h)).conj
@[simp] lemma homotopyEquivFundamentalGroupOfEq_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) {x : X} {y : Y} (h : e x = y)
    (γ : FundamentalGroup X x) :
    homotopyEquivFundamentalGroupOfEq e h γ = FundamentalGroup.mapOfEq e.toFun h γ := rfl
/-- The explicit radius-half basepoint of the annulus. -/
def annulusBasepoint : Annulus := halfCircle 1
@[simp] lemma annulusPolar_basepoint : annulusPolar annulusBasepoint = 1 :=
  annulusPolar_halfCircle 1
/-- The genuine based fundamental group isomorphism induced by polar normalization. -/
def annulusFundamentalGroupEquivCircle :
    FundamentalGroup Annulus annulusBasepoint ≃* FundamentalGroup Circle (1 : Circle) :=
  homotopyEquivFundamentalGroupOfEq annulusHomotopyEquivCircle annulusPolar_basepoint
@[simp] lemma annulusFundamentalGroupEquivCircle_apply
    (γ : FundamentalGroup Annulus annulusBasepoint) :
    annulusFundamentalGroupEquivCircle γ =
      FundamentalGroup.mapOfEq annulusPolar annulusPolar_basepoint γ := rfl
/-- The concrete loop `t ↦ (1/2) exp(2πt)` in the annulus. -/
def annulusGenerator : Path annulusBasepoint annulusBasepoint :=
  circleGenerator.map halfCircle.continuous
/-- The homotopy class of the concrete radius-half positive circle. -/
def annulusGeneratorClass : FundamentalGroup Annulus annulusBasepoint :=
  .mk annulusGenerator
@[simp] lemma annulusGenerator_coordinate (t : unitInterval) :
    annulusCoordinate (annulusGenerator t) =
      (1 / 2 : ℝ) • (Circle.exp ((t : ℝ) * (2 * Real.pi)) : ℂ) := rfl
/-- Polar projection identifies the half-radius generator with the standard generator. -/
lemma annulusPolar_generator :
    (annulusGenerator.map annulusPolar.continuous).cast
      annulusPolar_basepoint.symm annulusPolar_basepoint.symm = circleGenerator := by
  apply Path.ext
  funext t
  exact annulusPolar_halfCircle (circleGenerator t)
@[simp] lemma annulusFundamentalGroupEquivCircle_generator :
    annulusFundamentalGroupEquivCircle annulusGeneratorClass = circleGeneratorClass := by
  rw [annulusFundamentalGroupEquivCircle_apply, FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk
    ((annulusGenerator.map annulusPolar.continuous).cast
      annulusPolar_basepoint.symm annulusPolar_basepoint.symm) = _
  rw [annulusPolar_generator]
  rfl
/-- Every actual based annulus class is an integer power of the explicit half-radius loop. -/
theorem annulusGenerator_generates (γ : FundamentalGroup Annulus annulusBasepoint) :
    ∃ n : ℤ, annulusGeneratorClass ^ n = γ := by
  obtain ⟨n, hn⟩ := circleGenerator_generates (annulusFundamentalGroupEquivCircle γ)
  refine ⟨n, annulusFundamentalGroupEquivCircle.injective ?_⟩
  rw [map_zpow, annulusFundamentalGroupEquivCircle_generator]
  exact hn
/-- The concrete annulus loop generates the whole actual fundamental group. -/
theorem annulusGenerator_zpowers_eq_top : Subgroup.zpowers annulusGeneratorClass = ⊤ := by
  apply top_unique
  intro γ _
  exact annulusGenerator_generates γ
/-- Winding numbers give an actual isomorphism of the annulus fundamental group with ℤ. -/
def annulusFundamentalGroupEquivInt :
    FundamentalGroup Annulus annulusBasepoint ≃* Multiplicative ℤ :=
  annulusFundamentalGroupEquivCircle.trans circleFundamentalGroupEquivInt
@[simp] theorem annulusFundamentalGroupEquivInt_generator :
    annulusFundamentalGroupEquivInt annulusGeneratorClass = Multiplicative.ofAdd (1 : ℤ) := by
  change circleFundamentalGroupEquivInt
    (annulusFundamentalGroupEquivCircle annulusGeneratorClass) = _
  rw [annulusFundamentalGroupEquivCircle_generator]
  exact circleFundamentalGroupEquivInt_generator
/-- The coordinate-defined open disk is exactly the ordinary convex metric ball. -/
lemma openDisk_eq_ball : {z : ℂ | ‖z‖ < 1} = Metric.ball (0 : ℂ) 1 := by
  ext z
  simp [Metric.mem_ball, dist_zero_right]
/-- Contractibility comes from actual convex ball geometry. -/
instance openDisk_contractibleSpace : ContractibleSpace OpenDisk := by
  have hc : Convex ℝ {z : ℂ | ‖z‖ < 1} := by
    rw [openDisk_eq_ball]
    exact convex_ball (0 : ℂ) 1
  exact hc.contractibleSpace ⟨0, by simp⟩
/-- In particular the genuine open disk is simply connected. -/
instance openDisk_simplyConnectedSpace : SimplyConnectedSpace OpenDisk := inferInstance
end CellAttachment
end
end CellAttachment_Annulus
/-! Source module: CellAttachment.OpenCover -/
section CellAttachment_OpenCover
/-!
# The genuine two-open-set cover of an arbitrary cell attachment
The first open set omits exactly the disk centers. The second is the disjoint
union of all disk interiors. These facts use the quotient topology directly.
-/
noncomputable section
namespace CellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
/-- The center of the closed complex unit disk. -/
def diskCenter : Disk := ⟨0, by simp⟩
/-- The center viewed in the open disk. -/
def openDiskCenter : OpenDisk := ⟨0, by simp⟩
/-- The set of all attached disk interiors. -/
def interiors (f : ι → C(Circle, X)) : Set (Space f) :=
  {y | ∃ z : Σ _ : ι, OpenDisk, normalForm f y = .inr z}
/-- The set of attached disk centers, with no finiteness assumption. -/
def centers (f : ι → C(Circle, X)) : Set (Space f) :=
  {y | ∃ i : ι, normalForm f y = .inr ⟨i, openDiskCenter⟩}
/-- The punctured neighborhood of the original space. -/
def puncturedNeighborhood (f : ι → C(Circle, X)) : Set (Space f) := (centers f)ᶜ
@[simp] theorem inclusion_not_mem_interiors (f : ι → C(Circle, X)) (x : X) :
    inclusion f x ∉ interiors f := by simp [interiors]
@[simp] theorem interiorRepresentative_mem_interiors (f : ι → C(Circle, X))
    (i : ι) (z : OpenDisk) :
    quotientMap f (interiorRepresentative i z) ∈ interiors f := by
  exact ⟨⟨i, z⟩, normalForm_interiorRepresentative f i z⟩
@[simp] theorem inclusion_not_mem_centers (f : ι → C(Circle, X)) (x : X) :
    inclusion f x ∉ centers f := by simp [centers]
@[simp] theorem quotient_inl_mem_interiors (f : ι → C(Circle, X)) (x : X) :
    quotientMap f (.inl x) ∈ interiors f ↔ False := by
  change inclusion f x ∈ interiors f ↔ False
  simp
@[simp] theorem quotient_inr_mem_interiors (f : ι → C(Circle, X)) (i : ι) (z : Disk) :
    quotientMap f (.inr ⟨i, z⟩) ∈ interiors f ↔ ‖(z : ℂ)‖ < 1 := by
  change (∃ n, normalize f (.inr ⟨i, z⟩) = Sum.inr n) ↔ _
  by_cases h : ‖(z : ℂ)‖ = 1
  · simp [normalize, h]
  · simp [normalize, h, lt_of_le_of_ne z.property h]
@[simp] theorem quotient_inl_mem_centers (f : ι → C(Circle, X)) (x : X) :
    quotientMap f (.inl x) ∈ centers f ↔ False := by
  change inclusion f x ∈ centers f ↔ False
  simp
@[simp] theorem quotient_inr_mem_centers (f : ι → C(Circle, X)) (i : ι) (z : Disk) :
    quotientMap f (.inr ⟨i, z⟩) ∈ centers f ↔ (z : ℂ) = 0 := by
  change (∃ j, normalize f (.inr ⟨i, z⟩) = Sum.inr ⟨j, openDiskCenter⟩) ↔ _
  by_cases h : ‖(z : ℂ)‖ = 1
  · simp only [normalize, h, dite_true, Sum.inl_ne_inr, exists_false, false_iff]
    intro hz
    simpa [hz] using h
  · simp only [normalize, h, dite_false]
    constructor
    · rintro ⟨j, hj⟩
      have hz := congrArg (fun n : NormalForm X ι =>
        n.elim (fun _ => none) (fun w => some (w.2 : ℂ))) hj
      exact Option.some.inj hz
    · intro hz
      refine ⟨i, ?_⟩
      congr 2
      exact Subtype.ext hz
/-- Openness is checked on the unglued topological sum, component by component. -/
theorem interiors_isOpen (f : ι → C(Circle, X)) : IsOpen (interiors f) := by
  rw [← (quotientMap_isQuotientMap f).isCoinducing.isOpen_preimage]
  rw [isOpen_sum_iff]
  constructor
  · convert isOpen_empty (X := X) using 1
    ext x
    simp
  · rw [isOpen_sigma_iff]
    intro i
    have hopen : IsOpen {z : Disk | ‖(z : ℂ)‖ < 1} :=
      isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
    convert hopen using 1
    ext z
    simp
/-- The set of centers is closed even when the original space is non-Hausdorff. -/
theorem centers_isClosed (f : ι → C(Circle, X)) : IsClosed (centers f) := by
  rw [← (quotientMap_isQuotientMap f).isCoinducing.isClosed_preimage]
  rw [isClosed_sum_iff]
  constructor
  · convert isClosed_empty (X := X) using 1
    ext x
    simp
  · rw [isClosed_sigma_iff]
    intro i
    have hclosed : IsClosed {z : Disk | (z : ℂ) = 0} :=
      isClosed_eq continuous_subtype_val continuous_const
    convert hclosed using 1
    ext z
    simp
theorem puncturedNeighborhood_isOpen (f : ι → C(Circle, X)) :
    IsOpen (puncturedNeighborhood f) := (centers_isClosed f).isOpen_compl
/-- The two genuine open sets cover the whole adjunction quotient. -/
theorem openCover_union (f : ι → C(Circle, X)) :
    puncturedNeighborhood f ∪ interiors f = Set.univ := by
  ext y
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases h : y ∈ centers f
  · right
    rcases h with ⟨i, hi⟩
    exact ⟨⟨i, openDiskCenter⟩, hi⟩
  · exact Or.inl h
end CellAttachment
end
end CellAttachment_OpenCover
/-! Source module: CellAttachment.Embeddings -/
section CellAttachment_Embeddings
/-!
# Genuine embeddings in the attaching quotient
The original space is a closed embedded subspace, without any separation
assumption on it. The coproduct of disk interiors is openly embedded. Both
proofs use the quotient topology and the explicit attaching relation.
-/
noncomputable section
namespace CellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
/-- Boundary inclusion is closed because its domain is compact and its
codomain is Hausdorff. This does not require any separation of the base. -/
theorem boundaryInclusion_isClosedMap : IsClosedMap boundaryInclusion :=
  boundaryInclusion.continuous.isClosedMap
/-- The part of a closed base image lying over a particular disk is exactly
its attaching-boundary preimage. -/
theorem quotient_inr_mem_inclusion_image (f : ι → C(Circle, X))
    (A : Set X) (i : ι) (z : Disk) :
    quotientMap f (.inr ⟨i, z⟩) ∈ inclusion f '' A ↔
      z ∈ boundaryInclusion '' ((f i) ⁻¹' A) := by
  constructor
  · rintro ⟨x, hx, heq⟩
    have hn := congrArg (normalForm f) heq
    change normalize f (.inl x) = normalize f (.inr ⟨i, z⟩) at hn
    by_cases hz : ‖(z : ℂ)‖ = 1
    · simp only [normalize, hz, dite_true, Sum.inl.injEq] at hn
      refine ⟨diskBoundaryPoint z hz, ?_, ?_⟩
      · change f i (diskBoundaryPoint z hz) ∈ A
        simpa only [← hn] using hx
      · rfl
    · simp only [normalize, hz, dite_false, Sum.inl_ne_inr] at hn
  · rintro ⟨w, hw, rfl⟩
    exact ⟨f i w, hw, (characteristic_boundary f i w).symm⟩
/-- Closed subsets of the original space have closed images in the quotient. -/
theorem inclusion_isClosedMap (f : ι → C(Circle, X)) : IsClosedMap (inclusion f) := by
  intro A hA
  rw [← (quotientMap_isQuotientMap f).isCoinducing.isClosed_preimage]
  rw [isClosed_sum_iff]
  constructor
  · convert hA using 1
    ext x
    change inclusion f x ∈ inclusion f '' A ↔ x ∈ A
    exact (inclusion_injective f).mem_set_image
  · rw [isClosed_sigma_iff]
    intro i
    have hc := boundaryInclusion_isClosedMap ((f i) ⁻¹' A)
      (hA.preimage (f i).continuous)
    convert hc using 1
    ext z
    exact quotient_inr_mem_inclusion_image f A i z
/-- The original space is a closed embedded subspace for every attaching
family, including non-Hausdorff spaces and infinitely many disks. -/
theorem inclusion_isClosedEmbedding (f : ι → C(Circle, X)) :
    Topology.IsClosedEmbedding (inclusion f) :=
  .of_continuous_injective_isClosedMap (inclusion f).continuous
    (inclusion_injective f) (inclusion_isClosedMap f)
/-- The closed original-space image is exactly the complement of the
open disk interiors. -/
theorem inclusion_range_eq_compl_interiors (f : ι → C(Circle, X)) :
    Set.range (inclusion f) = (interiors f)ᶜ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact inclusion_not_mem_interiors f x
  · intro hy
    obtain ⟨a, rfl⟩ := (quotientMap_isQuotientMap f).surjective y
    cases a with
    | inl x => exact ⟨x, rfl⟩
    | inr w =>
      rcases w with ⟨i, z⟩
      have hn : ¬ ‖(z : ℂ)‖ < 1 := by
        simpa only [Set.mem_compl_iff, quotient_inr_mem_interiors] using hy
      have hz : ‖(z : ℂ)‖ = 1 := le_antisymm z.property (le_of_not_gt hn)
      refine ⟨f i (diskBoundaryPoint z hz), ?_⟩
      exact (characteristic_boundary f i (diskBoundaryPoint z hz)).symm
/-- The original space is homeomorphic to its closed image. -/
def inclusionHomeomorph (f : ι → C(Circle, X)) :
    X ≃ₜ Set.range (inclusion f) :=
  (inclusion_isClosedEmbedding f).isEmbedding.toHomeomorph
@[simp] theorem inclusionHomeomorph_apply (f : ι → C(Circle, X)) (x : X) :
    (inclusionHomeomorph f x : Space f) = inclusion f x := rfl
/-- The canonical map from the open complex disk into the closed disk. -/
def openDiskInclusion : C(OpenDisk, Disk) where
  toFun z := ⟨z, z.property.le⟩
  continuous_toFun := by fun_prop
theorem openDiskInclusion_isOpenMap : IsOpenMap openDiskInclusion := by
  have h : IsOpen {z : ℂ | ‖z‖ < 1} := isOpen_lt continuous_norm continuous_const
  exact h.isOpenMap_subtype_val.subtype_mk (p := fun z : ℂ => ‖z‖ ≤ 1) (fun z => (z.property : ‖(z : ℂ)‖ < 1).le)
/-- The coproduct of all interiors, included in the unglued topological sum. -/
def rawInteriorMap : C((Σ _ : ι, OpenDisk), Raw X ι) where
  toFun z := interiorRepresentative z.1 z.2
  continuous_toFun := by
    apply continuous_sigma
    intro i
    exact continuous_inr.comp ((continuous_sigmaMk (i := i)).comp
      openDiskInclusion.continuous)
/-- Interior inclusion is open already before taking the attaching quotient. -/
theorem rawInteriorMap_isOpenMap : IsOpenMap (rawInteriorMap (X := X) (ι := ι)) := by
  rw [isOpenMap_sigma]
  intro i
  exact isOpenMap_inr.comp (isOpenMap_sigmaMk.comp openDiskInclusion_isOpenMap)
/-- The canonical continuous inclusion of the coproduct of open disks. -/
def interiorMap (f : ι → C(Circle, X)) : C((Σ _ : ι, OpenDisk), Space f) :=
  (quotientMap f).comp rawInteriorMap
@[simp] theorem interiorMap_apply (f : ι → C(Circle, X)) (z : Σ _ : ι, OpenDisk) :
    interiorMap f z = quotientMap f (interiorRepresentative z.1 z.2) := rfl
/-- A raw interior representative has no other raw representative in its
quotient class. Boundary gluings do not affect it. -/
theorem quotient_eq_interiorRepresentative_iff (f : ι → C(Circle, X))
    (a : Raw X ι) (i : ι) (z : OpenDisk) :
    quotientMap f a = quotientMap f (interiorRepresentative i z) ↔
      a = interiorRepresentative i z := by
  constructor
  · intro heq
    have hn := congrArg (normalForm f) heq
    rw [normalForm_interiorRepresentative] at hn
    change normalize f a = Sum.inr ⟨i, z⟩ at hn
    cases a with
    | inl x => simp only [normalize, Sum.inl_ne_inr] at hn
    | inr w =>
      rcases w with ⟨j, w⟩
      by_cases hw : ‖(w : ℂ)‖ = 1
      · simp only [normalize, hw, dite_true, Sum.inl_ne_inr] at hn
      · simp only [normalize, hw, dite_false, Sum.inr.injEq] at hn
        have hraw := congrArg (fun p : Σ _ : ι, OpenDisk =>
          normalRepresentative (X := X) (Sum.inr p)) hn
        exact hraw
  · rintro rfl
    rfl
/-- Images of sets of interior points are saturated without adding any
boundary or original-space points. -/
theorem interiorMap_image_preimage (f : ι → C(Circle, X))
    (S : Set (Σ _ : ι, OpenDisk)) :
    (quotientMap f) ⁻¹' (interiorMap f '' S) = rawInteriorMap '' S := by
  ext a
  constructor
  · rintro ⟨z, hz, heq⟩
    refine ⟨z, hz, ?_⟩
    exact ((quotient_eq_interiorRepresentative_iff f a z.1 z.2).mp heq.symm).symm
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
/-- Interior images are open by checking their saturated raw preimages.
The global quotient map is not assumed to be open. -/
theorem interiorMap_isOpenMap (f : ι → C(Circle, X)) : IsOpenMap (interiorMap f) := by
  intro S hS
  rw [← (quotientMap_isQuotientMap f).isCoinducing.isOpen_preimage]
  rw [interiorMap_image_preimage]
  exact rawInteriorMap_isOpenMap S hS
/-- The entire coproduct of open disks openly embeds in the adjunction space. -/
theorem interiorMap_isOpenEmbedding (f : ι → C(Circle, X)) :
    Topology.IsOpenEmbedding (interiorMap f) :=
  .of_continuous_injective_isOpenMap (interiorMap f).continuous
    (interiors_injective f) (interiorMap_isOpenMap f)
/-- The range of the open embedding is precisely the open set of interiors. -/
theorem interiorMap_range (f : ι → C(Circle, X)) :
    Set.range (interiorMap f) = interiors f := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact interiorRepresentative_mem_interiors f z.1 z.2
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    obtain ⟨a, rfl⟩ := (quotientMap_isQuotientMap f).surjective y
    change normalize f a = Sum.inr z at hz
    exact (quotient_eq_iff_normalize_eq f _ _).mpr (by
      change normalize f (normalRepresentative (Sum.inr z)) = normalize f a
      rw [normalize_normalRepresentative f (Sum.inr z)]
      exact hz.symm)
/-- The disjoint union of disk interiors is homeomorphic to the actual
interior subspace, with its induced quotient topology. -/
def interiorsHomeomorph (f : ι → C(Circle, X)) :
    (Σ _ : ι, OpenDisk) ≃ₜ interiors f :=
  (interiorMap_isOpenEmbedding f).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (interiorMap_range f))
@[simp] theorem interiorsHomeomorph_apply (f : ι → C(Circle, X))
    (z : Σ _ : ι, OpenDisk) :
    (interiorsHomeomorph f z : Space f) = interiorMap f z := rfl
end CellAttachment
end
end CellAttachment_Embeddings
/-! Source module: Lean4.fraction -/
section Lean4_fraction
open scoped unitInterval
noncomputable section
theorem div_add_div_same (a b c : ℝ) :
    a / c + b / c = (a + b) / c := by
  rw [add_div]
/--
For any natural numbers `i n : ℕ` such that `n` is positive and `i ≤ n`, we have that the fraction
`i/n : ℝ` lives in the unit interval
-/
@[reducible]
def Fraction {i n : ℕ} (hn : 0 < n) (hi : i ≤ n) : I :=
  ⟨(i : ℝ)/(n : ℝ), ⟨div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg n), (div_le_one (Nat.cast_pos.mpr hn)).mpr (Nat.cast_le.mpr hi)⟩⟩
namespace Fraction
/--
For any positive number `n : ℕ`, we have the fraction `1/n : ℝ` in the unit interval
-/
@[reducible]
def ofPos {n : ℕ} (hn : 0 < n) : I := Fraction hn (Nat.succ_le_iff.mpr hn)
@[simp]
lemma Fraction_coe {i n : ℕ} (hn : 0 < n) (hi : i ≤ n) : (Fraction hn hi : ℝ) = (i/n : ℝ) := rfl
@[simp]
lemma ofPos_coe {n : ℕ} (hn : 0 < n) : ((ofPos hn) : ℝ) = (1/n : ℝ) := by simp
/--
For any postive `n : ℕ`, we have that `0/n = n`.
-/
lemma eq_zero {n : ℕ} (n_pos : 0 < n) : Fraction n_pos (Nat.zero_le n) = 0 := by
  ext
  rw [Fraction_coe]
  simp
/--
For any postive `n : ℕ`, we have that `n/n = n`.
-/
lemma eq_one {n : ℕ} (n_pos : 0 < n) : Fraction n_pos (le_refl n) = 1 := by
  ext
  rw [Fraction_coe, div_self]
  simp
  exact Nat.cast_ne_zero.mpr (ne_of_gt n_pos)
/--
For any `i n : ℕ` with `0 < i ≤ n`, we have that `i/n * 1/i` = `1/n` as members of `I`.
-/
lemma mul_inv {i n : ℕ} (i_pos : 0 < i) (hi_n : i ≤ n) :
    (Fraction (lt_of_lt_of_le i_pos hi_n) hi_n) * (ofPos i_pos) = (ofPos (lt_of_lt_of_le i_pos hi_n)) := by
  apply Subtype.coe_inj.mp
  simp
  calc (i : ℝ)/n * (↑i)⁻¹
    _ = (i * (↑i)⁻¹)/↑n  := div_mul_eq_mul_div (i : ℝ) n i⁻¹
    _ = 1/n              := by rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt i_pos))]
    _ = (↑n)⁻¹           := one_div (n : ℝ)
/--
For any `n i : ℕ` with `0 < i ≤ n`, we have that `0 < i/n`.
-/
lemma pos_of_pos {n i : ℕ} (hi : 0 < i) (hn : i ≤ n) : 0 < Fraction (lt_of_lt_of_le hi hn) hn :=
  Subtype.coe_lt_coe.mp (div_pos (Nat.cast_pos.mpr hi) (Nat.cast_pos.mpr (lt_of_lt_of_le hi hn)))
/--
For any `n i : ℕ` with `0 ≤ i < n`, we have that `i/n < 1`.
-/
lemma lt_one_of_lt {n i : ℕ} (hi : 0 ≤ i) (hn : i < n) : Fraction (lt_of_le_of_lt hi hn) (le_of_lt hn) < 1 :=
  Subtype.coe_lt_coe.mp ((div_lt_one (Nat.cast_pos.mpr (lt_of_le_of_lt hi hn))).mpr (Nat.cast_lt.mpr hn))
/-
For any positive `n : ℕ`, we have that `0 < 1/n`.
-/
lemma ofPos_pos {n : ℕ} (hn : 0 < n) : 0 < ofPos hn := pos_of_pos zero_lt_one (Nat.succ_le_iff.mpr hn)
/-
For any `n : ℕ` with `n > 1`, we have that `1/n < 1`.
-/
lemma ofPos_lt_one {n : ℕ} (hn : 1 < n) : ofPos (lt_trans zero_lt_one hn) < 1 := lt_one_of_lt zero_le_one hn
/-
For any `n m : ℕ` with `m < n`, we have that `m/n ≤ (m+1) ≤ n`
-/
lemma lt_frac_succ {n m : ℕ} (hn : m < n) :
    Fraction (lt_of_le_of_lt (Nat.zero_le m) hn) (le_of_lt hn) <
    Fraction (lt_of_le_of_lt (Nat.zero_le m) hn) (Nat.succ_le_of_lt hn) := by
  apply Subtype.coe_lt_coe.mp
  exact div_lt_div_of_pos_right
    (show (m : ℝ) < (Nat.succ m : ℝ) by exact_mod_cast Nat.lt_succ_self m)
    (show (0 : ℝ) < (n : ℝ) by
      exact_mod_cast lt_of_le_of_lt (Nat.zero_le m) hn)
end Fraction
end
end Lean4_fraction
/-! Source module: Lean4.cover_lemma -/
section Lean4_cover_lemma
/-
  This file contains two applications of the Lebesgue Number Lemma:
  One concerns the unit interval and the other concerns the unit square.
-/
universe u
open scoped unitInterval
/-! ### Auxiliary lemmas -/
/--
For any two natural numbers `i n : ℕ` with `n > 0`, we have that
`(2i+1)/(2n)` is contained in the interval `[i/n, (i+1)/n]`.
-/
lemma mid_point_Icc {i n : ℕ} (hn : n > 0) :
    (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ Set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) := by
  constructor <;>
  refine' (div_le_div_iff₀ (by positivity) (by positivity)).mpr _ <;>
  linarith [show (n : ℝ) > 0 by exact Nat.cast_pos.mpr hn]
/--
For any two natural numbers `i n : ℕ` with `i < n`, we have that
`(2i+1)/(2n)` is contained in unit interval
-/
lemma mid_point_I {i n : ℕ} (hi : i < n) : (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ I := by
  have n_cast_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le i) hi)
  have : 2 * i + 1 ≤ 2 * n := by linarith
  constructor
  · apply div_nonneg
    exact add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg i)) (by norm_num)
    exact mul_nonneg (by norm_num) (Nat.cast_nonneg n)
  · refine' (div_le_one (mul_pos (by norm_num) n_cast_pos)).mpr _
    have : (↑(2 * i  + 1) : ℝ) ≤ ↑(2 * n) := Nat.cast_le.mpr this
    convert this <;> simp
namespace UnitIntervalSub
open Set
lemma mem_I_of_mem_interval {t : ℝ} {n i : ℕ} (hi : i < n.succ) (h : t ∈ Icc ((i:ℝ)/↑(n.succ)) (↑(i+1)/↑(n.succ))) :
    t ∈ I := by
  constructor
  exact le_trans (div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg n.succ)) h.1
  exact le_trans h.2 ((div_le_one (show (n.succ : ℝ) > 0 by
    exact Nat.cast_pos.mpr (Nat.succ_pos n))).mpr (Nat.cast_le.mpr (Nat.succ_le_of_lt hi)))
lemma mem_I_of_mem_interval_coed {t : ℝ} {n i : ℕ} (hi : i < n.succ) (h : t ∈ Icc ((i:ℝ)/(↑n+1)) ((↑i+1)/(↑n+1))) :
    t ∈ I := by
  apply mem_I_of_mem_interval hi
  convert h <;> exact Nat.cast_succ _
end UnitIntervalSub
/-! ### Covering lemma for the unit interval -/
theorem lebesgue_number_lemma_unit_interval {ι : Sort u} {c : ι → Set ℝ}
  (hc₁ : ∀ (i : ι), IsOpen (c i)) (hc₂ : I ⊆ ⋃ (i : ι), c i) :
    ∃ (n : ℕ), (n > 0) ∧ ∀ (i : ℕ) (h : i < n), ∃ (j : ι), Set.Icc ((i : ℝ)/n) ((i+1)/n) ⊆ c j := by
  rcases (lebesgue_number_lemma_of_metric (isCompact_Icc) hc₁ hc₂) with ⟨δ, δ_pos, hδ⟩
  rcases Real.instArchimedean.arch 2 δ_pos with ⟨n, hn⟩
  use n
  have n_pos : 0 < n := by
    by_contra
    have : n = 0 := by linarith
    rw [this] at hn
    have : (2 : ℝ) ≤ 0 := hn
    linarith
  have n_cast_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr n_pos
  constructor
  · exact n_pos
  intros i hi
  have mid_point_I : (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ I := mid_point_I hi
  have mid_point_Icc : (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ Set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) := mid_point_Icc n_pos
  rcases (hδ ((2 * i + 1 : ℝ)/(2 * n : ℝ)) mid_point_I) with ⟨j, hj⟩
  use j
  apply subset_trans _ hj
  intros x hx
  show dist x ((2 * i + 1 : ℝ)/(2 * n : ℝ)) < δ
  have : 1/(n : ℝ) < δ := by
    apply (div_lt_iff₀ n_cast_pos).mpr
    have hn' : (2 : ℝ) ≤ (n : ℝ) * δ := by simpa [nsmul_eq_mul] using hn
    calc
      1 < 2 := by norm_num
      _ ≤ δ * (n : ℝ) := by simpa [mul_comm] using hn'
  apply lt_of_le_of_lt _ this
  apply le_trans (Real.dist_le_of_mem_Icc hx mid_point_Icc)
  rw [div_sub_div_same]
  simp
/-! ### Covering lemma for the unit square -/
def UnitSquare : Set (I × I) := Set.univ
lemma compact_unitSquare : IsCompact UnitSquare := isCompact_univ
/--
For any four natural numbers `n m i j : ℕ` such that `i < n + 1` and `j < m + 1`,
we have the rectangle `[i/(n+1), (i+1)/(n+1)] × [j/(m+1), (j+1)/(m+1)]` in the unit square.
-/
def UnitSubrectangle {n m i j : ℕ} (hi : i < n.succ) (hj : j < m.succ) : Set (I × I) :=  setOf $
  fun (a : I × I) =>
    ((Fraction (Nat.succ_pos n) (le_of_lt hi)) ≤ a.1 ∧ a.1 ≤ (Fraction (Nat.succ_pos n) (Nat.succ_le_of_lt hi))) ∧
    (Fraction (Nat.succ_pos m) (le_of_lt hj)) ≤ a.2 ∧ a.2 ≤ (Fraction (Nat.succ_pos m) (Nat.succ_le_of_lt hj))
namespace UnitSubrectangle
open Set
lemma mem_unitSquare (t : I × I) : t ∈ UnitSubrectangle zero_lt_one zero_lt_one := by
  unfold UnitSubrectangle
  rw [Fraction.eq_zero, Fraction.eq_one]
  exact ⟨⟨t.1.2.1, t.1.2.2⟩, ⟨t.2.2.1, t.2.2.2⟩⟩
lemma mem_unitSubrectangle {t₀ t₁ : ℝ} {n m i j : ℕ} (hi : i < n.succ) (hj : j < m.succ)
  (ht₀ : t₀ ∈ Icc ((i : ℝ)/↑(n.succ)) (↑(i+1)/↑(n.succ))) (ht₁ : t₁ ∈ Icc ((j : ℝ)/↑(m.succ)) (↑(j+1)/↑(m.succ))) :
    ((⟨t₀, UnitIntervalSub.mem_I_of_mem_interval hi ht₀⟩ : I),
      (⟨t₁, UnitIntervalSub.mem_I_of_mem_interval hj ht₁⟩ : I)) ∈ UnitSubrectangle hi hj :=
  ⟨⟨ht₀.1, ht₀.2⟩, ⟨ht₁.1, ht₁.2⟩⟩
end UnitSubrectangle
theorem lebesgue_number_lemma_unit_square {ι : Sort u} {c : ι → Set (I × I)}
  (hc₁ : ∀ (i : ι), IsOpen (c i)) (hc₂ : UnitSquare ⊆ (⋃ (i : ι), c i)) :
    ∃ (n : ℕ), ∀ (i j : ℕ) (hi : i < n.succ) (hj : j < n.succ), ∃ (a : ι), UnitSubrectangle hi hj ⊆ c a := by
  rcases (lebesgue_number_lemma_of_metric (compact_unitSquare) hc₁ hc₂) with ⟨δ, δ_pos, hδ⟩
  rcases Real.instArchimedean.arch 2 δ_pos with ⟨n, hn⟩
  use n
  have n_pos : 0 < n.succ := Nat.succ_pos n
  have n_cast_pos : 0 < (n.succ : ℝ) := Nat.cast_pos.mpr n_pos
  intros i j hi hj
  let mp_h : ℝ := (2 * i + 1 : ℝ)/(2 * n.succ : ℝ)
  let mp_v : ℝ := (2 * j + 1 : ℝ)/(2 * n.succ : ℝ)
  have mid_point_h_Icc : mp_h ∈ Set.Icc ((i:ℝ)/n.succ) ((i+1)/n.succ) := mid_point_Icc n_pos
  have mid_point_h_I : mp_h ∈ I := mid_point_I hi
  have mid_point_v_Icc : mp_v ∈ Set.Icc ((j:ℝ)/(n.succ:ℝ)) ((j+1:ℝ)/(n.succ:ℝ)) := mid_point_Icc n_pos
  have mid_point_v_I : mp_v ∈ I := mid_point_I hj
  rcases hδ (⟨mp_h, mid_point_h_I⟩, ⟨mp_v, mid_point_v_I⟩) (Set.mem_univ _) with ⟨a, ha⟩
  use a
  apply subset_trans _ ha
  intros x hx
  show dist x _ < δ
  have : dist _ _ ≤ dist _ _ + dist _ _ := dist_triangle x (x.1, ⟨mp_v, mid_point_v_I⟩)  (⟨mp_h, mid_point_h_I⟩, ⟨mp_v, mid_point_v_I⟩)
  apply lt_of_le_of_lt this
  have : 1/(n.succ : ℝ) < δ/2 := by
    apply (div_lt_iff₀ n_cast_pos).mpr
    have hn' : (2 : ℝ) ≤ (n : ℝ) * δ := by simpa [nsmul_eq_mul] using hn
    have hsucc : (2 : ℝ) < (n.succ : ℝ) * δ := by
      rw [Nat.cast_succ]
      nlinarith [δ_pos, hn']
    calc
      1 < ((n.succ : ℝ) * δ) / 2 := by nlinarith [hsucc]
      _ = δ / 2 * (n.succ : ℝ) := by ring
  have h₁ : dist x (x.1, ⟨mp_v, mid_point_v_I⟩) < (δ/2) := by
    apply lt_of_le_of_lt _ this
    have : x = (x.1, x.2) := by ext <;> rfl
    rw [this, dist_prod_same_left]
    convert Real.dist_le_of_mem_Icc hx.2 _ using 1
    simp
    rw [div_sub_div_same]
    simp
    convert mid_point_v_Icc using 2
    rw [Fraction.Fraction_coe, Nat.cast_succ]
  have h₂ : dist (x.1, (⟨mp_v, mid_point_v_I⟩ : I)) ((⟨mp_h, mid_point_h_I⟩ :I), (⟨mp_v, mid_point_v_I⟩ : I)) < (δ/2) := by
    apply lt_of_le_of_lt _ this
    rw [dist_prod_same_right]
    convert Real.dist_le_of_mem_Icc hx.1 _ using 1
    simp
    rw [div_sub_div_same]
    simp
    convert mid_point_h_Icc using 2
    rw [Fraction.Fraction_coe, Nat.cast_succ]
  linarith
end Lean4_cover_lemma
/-! Source module: Lean4.directed_space -/
section Lean4_directed_space
namespace Path
/-- Compatibility name for the unit-interval endpoint lemma used by the source port. -/
theorem extend_extends {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : γ.extend t = γ ⟨t, ht⟩ := by
  exact extend_extends' γ ⟨t, ht⟩
end Path
/-
  # Definition of directed spaces
  This file defines the directed space, an extension of a topological space where
  some of its paths are considered directed paths.
-/
universe u
open scoped unitInterval
/-- Definition of a directed topological space.
    Dipaths are closed under:
    * Constant paths,
    * Concatenation of paths,
    * Monotone reparametrization of paths
 -/
class DirectedSpace (α : Type u) extends TopologicalSpace α where
  IsDipath : ∀ {x y : α}, Path x y → Prop
  isDipath_constant : ∀ (x : α), IsDipath (Path.refl x)
  isDipath_concat : ∀ {x y z : α} {γ₁ : Path x y} {γ₂ : Path y z}, IsDipath γ₁ → IsDipath γ₂ → IsDipath (Path.trans γ₁ γ₂)
  isDipath_reparam : ∀ {x y : α} {γ : Path x y} {t₀ t₁ : I} {f : Path t₀ t₁}, Monotone f → IsDipath γ → IsDipath (f.map (γ.continuous_toFun))
section DirectedSpace
variable {α : Type u} {x y z : α} [DirectedSpace α] {γ : Path x y}  {γ' : Path y z} {t₀ t₁ : I} {f : Path t₀ t₁}
def IsDipath : (Path x y) → Prop :=
  DirectedSpace.IsDipath
def isDipath_constant (x : α) : IsDipath (Path.refl x) :=
  DirectedSpace.isDipath_constant _
def isDipath_concat (hγ : IsDipath γ) (hγ' : IsDipath γ') : IsDipath (γ.trans γ') :=
  DirectedSpace.isDipath_concat hγ hγ'
def isDipath_reparam (hfmono : Monotone f) (hγ : IsDipath γ) : IsDipath (f.map γ.continuous_toFun) :=
  DirectedSpace.isDipath_reparam hfmono hγ
/-- Casting a path that is directed into another path gives another directed path -/
lemma isDipath_cast {x y x' y' : α} (γ : Path x y) (hx : x' = x) (hy : y' = y) (hγ : IsDipath γ) :
  IsDipath (γ.cast hx hy) := by
    subst_vars
    simpa only [Path.cast_rfl_rfl] using hγ
end DirectedSpace
end Lean4_directed_space
/-! Source module: Lean4.directed_map -/
section Lean4_directed_map
/-
  # Definition of directed maps
  This file defines the directed map between two directed spaces `X` and `Y` :
  it is a continuous map from `X` to `Y` that is also `Directed`, i.e. it maps any dipath in `X` to a dipath in `Y`.
  We give the definitions of:
  * Constant maps
  * Identities
  * Composition of directed maps
-/
namespace DirectedMap
/-- A continuous map between two directed spaces is `Directed` if it maps dipaths to dipaths. -/
def Directed {α β : Type*} [DirectedSpace α] [DirectedSpace β] (f : C(α, β)) : Prop :=
  ∀ ⦃x y : α⦄ (γ : Path x y), IsDipath γ → IsDipath (γ.map f.continuous_toFun)
end DirectedMap
/-- Define the type of a directed map -/
structure DirectedMap (α β : Type*) [DirectedSpace α] [DirectedSpace β] extends ContinuousMap α β where
  protected directed_toFun : DirectedMap.Directed toContinuousMap
/-- Notation `D(X,Y)` for directed maps from `X` to `Y` -/
notation "D("α","β")" => DirectedMap α β
section
class DirectedMapClass (F : Type*) (α β : outParam <| Type*) [DirectedSpace α] [DirectedSpace β]
  [FunLike F α β] extends ContinuousMapClass F α β : Prop where
  map_directed (f : F) : DirectedMap.Directed (f : C(α, β))
end
export DirectedMapClass (map_directed)
section DirectedMapClass
variable {F α β : Type*} [DirectedSpace α] [DirectedSpace β] [FunLike F α β] [hF : DirectedMapClass F α β]
@[coe] def toDirectedMap (f : F) : D(α, β) := ⟨f, map_directed f⟩
instance : CoeTC F D(α, β) := ⟨toDirectedMap⟩
end DirectedMapClass
variable {α β γ δ : Type*} [DirectedSpace α] [DirectedSpace β] [DirectedSpace γ] [DirectedSpace δ]
namespace DirectedMap
instance instFunLike : FunLike D(α, β) α β where
  coe := fun f => f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
instance toDirectedMapClass : DirectedMapClass D(α, β) α β where
  map_continuous := fun f => f.continuous_toFun
  map_directed := fun f => f.directed_toFun
/-- A directed map can be coerced into a continuous map -/
instance : Coe D(α, β) C(α, β) := ⟨fun f => f.toContinuousMap⟩
@[simp] lemma toFun_eq_coe {f : D(α, β)} : f.toFun = (f : α → β) := rfl
@[simp] lemma coe_to_continuous_map (f : D(α, β)) : ⇑f.toContinuousMap = f := rfl
@[simp] protected lemma coe_coe {F : Type*} [FunLike F α β] [DirectedMapClass F α β] (f : F) : ⇑(f : D(α, β)) = f := rfl
@[ext] theorem ext {f g : D(α, β)} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h
variable (α)
/-- The identity map is directed -/
protected def id : D(α, α) where
  toFun := id
  directed_toFun := fun x y γ γ_path => γ_path
@[simp] lemma coe_id : ⇑(DirectedMap.id α) = id := rfl
/-- Constant maps are directed -/
def const (b : β) : D(α, β) where
  toFun := fun _ : α => b
  directed_toFun := fun x y γ _ => isDipath_constant b
@[simp] lemma coe_const (b : β) : ⇑(const α b) = Function.const α b := rfl
variable {α}
/-- The composition of directed maps is directed -/
def comp (f : D(β, γ)) (g : D(α, β)) : D(α, γ) where
  toFun := f ∘ g
  directed_toFun := fun x y p hp => f.directed_toFun (p.map g.continuous_toFun) (g.directed_toFun p hp)
@[simp] lemma id_apply (a : α) : DirectedMap.id α a = a := rfl
@[simp] lemma const_apply (b : β) (a : α) : const α b a = b := rfl
@[simp] lemma coe_comp (f : D(β, γ)) (g : D(α, β)) : ⇑(f.comp g) = f ∘ g := rfl
@[simp] lemma comp_apply (f : D(β, γ)) (g : D(α, β)) (a : α) : f.comp g a = f (g a) := rfl
@[simp] lemma comp_assoc (f : D(γ, δ)) (g : D(β, γ)) (h : D(α, β)) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma id_comp (f : D(α, β)) : (DirectedMap.id β).comp f = f := ext fun _ => rfl
@[simp] lemma comp_id (f : D(α, β)) : f.comp (DirectedMap.id α) = f := ext fun _ => rfl
@[simp] lemma const_comp (c : γ) (f : D(α, β)) : (const β c).comp f = const α c := ext $ fun _ => rfl
@[simp] lemma comp_const (f : D(β, γ)) (b : β) : f.comp (const α b) = const α (f b) := ext $ fun _ => rfl
lemma coe_injective : @Function.Injective D(α, β) (α → β) (↑) :=
  fun f g h => by cases f; cases g; congr; exact ContinuousMap.ext (congrFun h)
end DirectedMap
end Lean4_directed_map
/-! Source module: Lean4.monotone_path -/
section Lean4_monotone_path
/-
  This file contains lemmas about monotone paths in a preordered topological space
-/
open scoped unitInterval
lemma monotone_path_bounded_left {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) (t : I) : x ≤ γ t :=
    Eq.trans_le (id γ.source.symm) (hγ unitInterval.nonneg')
lemma monotone_path_bounded_right {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) (t : I) : γ t ≤ y :=
  calc
    γ t ≤ γ 1 := hγ (Subtype.coe_le_coe.mp (unitInterval.le_one t))
    _ = y := γ.target
lemma monotone_path_bounded {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) (t : I) : x ≤ γ t ∧ γ t ≤ y :=
  ⟨monotone_path_bounded_left hγ t, monotone_path_bounded_right hγ t⟩
lemma monotone_path_source_le_target {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) : x ≤ y :=
  calc
    x = γ 0 := γ.source.symm
    _ ≤ γ 1 := hγ (by norm_num : (0 : I) ≤ 1)
    _ = y := γ.target
end Lean4_monotone_path
/-! Source module: Lean4.constructions -/
section Lean4_constructions
/-
  This file contains constructions of directed spaces such as:
  * The directed space induced by a preorder on a topological space.
  * The directed space induced by a continuous map from a topological space to a directed space.
  * The product of two directed spaces.
  This file also contains lemmas about directed maps from/to these spaces.
-/
open DirectedMap
open scoped unitInterval
universe u v
/--
  Any space with a preorder can be equiped with a directedness, by allowing all monotone paths
  as directed paths
-/
def DirectedSpace.Preorder (α : Type u) [TopologicalSpace α] [Preorder α] :
    DirectedSpace α where
  IsDipath := fun {x y : α} γ => Monotone ↑γ
  isDipath_constant := fun x _ _ _ => le_refl x
  isDipath_concat := by
    intros x y z γ₁ γ₂ hγ₁ hγ₂ a b hab
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with h₁ h₂ h₂
    · -- a ≤ 1/2 and b ≤ 1/2, so use monotonicity of γ₁
      apply hγ₁
      simp
      exact hab
    · -- a ≤ 1/2 and b > 1/2, so use that γ₁ ≤ y ≤ γ₂
      exact le_trans (monotone_path_bounded hγ₁ _).2 (monotone_path_bounded hγ₂ _).1
    · -- Impossible, as 1/2 < a and b ≤ 1/2 and a ≤ b
      exact False.elim (h₁ (le_trans hab h₂))
    · -- a > 1/2 and b > 1/2, so use monotonicity of γ₂
      apply hγ₂
      simp
      exact hab
  isDipath_reparam := fun {x y : α} γ t₀ t₁ f hf_mono hγ_mono a b hab => hγ_mono (hf_mono hab)
/--
  A continuous map `f : α → β` with α an (undirected) topological space and β a directed topological space
  creates a directed structure on α by pulling back paths.
-/
def DirectedSpace.Induced {α : Type u} {β : Type v} [TopologicalSpace α] [hβ : DirectedSpace β]
  {f : α → β} (hf : Continuous f) : DirectedSpace α where
  IsDipath := fun {x y : α} γ => IsDipath (γ.map hf)
  isDipath_constant := fun x => isDipath_constant (f x)
  isDipath_concat := by
    rintro x y z γ₁ γ₂ hγ₁ hγ₂
    rw [Path.map_trans γ₁ γ₂ hf]
    exact isDipath_concat hγ₁ hγ₂
  isDipath_reparam := fun {x y : α} γ t₀ t₁ φ hφ_mono hγ => by
    exact isDipath_reparam hφ_mono hγ
instance DirectedSubspace {α : Type u} {p : α → Prop} [DirectedSpace α] :
  DirectedSpace (Subtype p) :=
  DirectedSpace.Induced continuous_induced_dom
section subtype
lemma directed_induced {α : Type u} {β : Type v} [TopologicalSpace α] [hβ : DirectedSpace β]
  (f : C(α, β)) :
  @DirectedMap.Directed α β (DirectedSpace.Induced f.continuous_toFun) hβ f := fun _ _ _ hγ => hγ
def DirectedSubtypeInclusion  {α : Type u} (p : α → Prop) [DirectedSpace α] : D(Subtype p, α) where
  toFun := λ x => ↑x
  continuous_toFun := continuous_induced_dom
  directed_toFun := directed_induced _
def DirectedSubsetInclusion {α : Type u} [t : DirectedSpace α] {X Y : Set α} (h : X ⊆ Y) : D(X, Y) where
  toFun := Set.inclusion h
  continuous_toFun := continuous_inclusion h
  directed_toFun := by
    intros x y γ γ_dipath
    have cont_X := @continuous_induced_dom {x // x ∈ X} α (fun p => ↑p)
    have cont_Y := @continuous_induced_dom {x // x ∈ Y} α (fun p => ↑p)
    have cont_X_Y : Continuous (Set.inclusion h) := continuous_inclusion h
    show IsDipath ((γ.map cont_X_Y).map cont_Y)
    have : (γ.map cont_X) = ((γ.map cont_X_Y).map cont_Y) := by { ext; rfl }
    rw [←this]
    exact γ_dipath
end subtype
instance DirectedProduct {α : Type u} {β : Type v} [t₁ : DirectedSpace α] [t₂ : DirectedSpace β] :
  DirectedSpace (α × β) where
  IsDipath := fun {x y : α × β} γ => (IsDipath (γ.map continuous_fst) ∧ IsDipath (γ.map continuous_snd))
  isDipath_constant := fun ⟨x₁, x₂⟩ => ⟨isDipath_constant x₁, isDipath_constant x₂⟩
  isDipath_concat := by
      rintro _ _ _ p q ⟨p₁_dipath, p₂_dipath⟩ ⟨q₁_dipath, q₂_dipath⟩
      convert (And.intro (isDipath_concat p₁_dipath q₁_dipath) (isDipath_concat p₂_dipath q₂_dipath))
      rw [Path.map_trans]
      rw [Path.map_trans]
  isDipath_reparam := fun {a b : α × β} γ t₀ t₁ φ hφ_mono ⟨γ₁_dipath, γ₂_dipath⟩ =>
      ⟨isDipath_reparam hφ_mono γ₁_dipath, isDipath_reparam hφ_mono γ₂_dipath⟩
/-- The projection map `α × β → α` -/
def directed_fst {α β : Type*} [DirectedSpace α] [DirectedSpace β] : D(α × β, α) where
  toFun := fun x => x.1
  directed_toFun := fun _ _ γ ⟨hγ₁, _⟩ => hγ₁
/-- The projection map `α × β → β` -/
def directed_snd {α β : Type*} [DirectedSpace α] [DirectedSpace β] : D(α × β, β) where
  toFun := fun x => x.2
  directed_toFun := fun _ _ γ ⟨_, hγ₂⟩ => hγ₂
section prod
variable {α β γ δ : Type*}  [DirectedSpace α] [DirectedSpace β] [DirectedSpace γ] [DirectedSpace δ]
/--
  Two directed maps `f : α → β` and `g : α → γ` can be turned into a directed map `α → β × γ` by
  mapping `a : α` to `(f a, g a)`.
-/
protected def DirectedMap.prod_map_mk (f : D(α, β)) (g : D(α, γ)) : D(α, β × γ) where
  toFun := fun x => (f x, g x)
  directed_toFun := fun x y γ hγ => ⟨f.directed_toFun γ hγ, g.directed_toFun γ hγ⟩
/--
  Two directed maps `f : α → γ` and `g : β → δ` can be turned into a directed map `α × β → β × γ` by
  mapping `(a, b) : α × β` to `(f a, g b)`.
-/
protected def DirectedMap.prod_map_mk' (f : D(α, γ)) (g : D(β, δ)) : D(α × β, γ × δ) where
  toFun := fun x => (f x.1, g x.2)
  directed_toFun := fun x y γ ⟨hγ₁, hγ₂⟩ => ⟨f.directed_toFun _ hγ₁, g.directed_toFun _ hγ₂⟩
/--
  For every `t : α`, we can convert a directed map `F : α × β → γ` to a directed map `β → γ` by
  sending `b` to `F(t, b)`
-/
def DirectedMap.prod_const_fst (F : D(α × β, γ)) (a : α) : D(β, γ) :=
  F.comp (DirectedMap.prod_map_mk (DirectedMap.const β a) (DirectedMap.id β))
@[simp] lemma DirectedMap.prod_const_fst_apply (F : D(α × β, γ)) (a : α) (b : β) :
  DirectedMap.prod_const_fst F a b = F (a, b) := rfl
/--
  For every `t : β`, we can convert a directed map `F : α × β → γ` to a directed map `α → γ` by
  sending `a` to `F(a, t)`
-/
def DirectedMap.prod_const_snd (F : D(α × β, γ)) (t : β) : D(α, γ) :=
  F.comp (DirectedMap.prod_map_mk (DirectedMap.id α) (DirectedMap.const α t))
@[simp] lemma DirectedMap.prod_const_snd_apply (F : D(α × β, γ)) (b : β) (a : α) :
  DirectedMap.prod_const_snd F b a = F (a, b) := rfl
end prod
end Lean4_constructions
/-! Source module: Lean4.directed_unit_interval -/
section Lean4_directed_unit_interval
/-
  This file contains the definition of the directed unit interval.
  The directedness is induced by the preorder it inherits from ℝ.
-/
open scoped unitInterval
universe u
namespace DirectedUnitInterval
/--
  Construct the directed unit interval by using the preorder inherited from ℝ
-/
instance : DirectedSpace I := DirectedSpace.Preorder I
/--
  The identity on I as a path I → I.
-/
def IdentityPath : Path (0 : I) (1 : I) :=
{
  toFun := fun x => x,
  continuous_toFun := by continuity,
  source' := by simp,
  target' := by simp,
}
/-- The identity path is a directed path. -/
lemma isDipath_identityPath : IsDipath IdentityPath := fun _ _ hab => hab
/--
  If `γ` is path and the identity path on I composed with `γ` is a directed path, then `γ` is a directed path.
-/
lemma isDipath_of_isDipath_comp_id {X : Type u} [DirectedSpace X] {x y : X} {γ : Path x y}
  (h : IsDipath $ IdentityPath.map γ.continuous_toFun) : IsDipath γ := by
  have hpath : (IdentityPath.map γ.continuous_toFun).cast γ.source.symm γ.target.symm = γ := by
    apply Path.ext
    funext t
    rfl
  rw [← hpath]
  exact isDipath_cast (IdentityPath.map γ.continuous_toFun) γ.source.symm γ.target.symm h
/-- A directed map from I to I is monotone -/
lemma monotone_of_directed (f : D(I, I)) : Monotone f :=
  fun _ _ h => (f.directed_toFun IdentityPath isDipath_identityPath) h
/-- A continuous map from I to I that is monotone is directed -/
lemma directed_of_monotone (f : C(I, I)) (hf_mono : Monotone f) : DirectedMap.Directed f :=
  fun _ _ _ γ_dipath _ _ ht₀t₁ => hf_mono (γ_dipath ht₀t₁)
/-- A directed path on I is bounded by its source and target -/
lemma directed_path_bounded {t₀ t₁ : I} {γ : Path t₀ t₁} (γ_dipath : IsDipath γ) : ∀ t, t₀ ≤ γ t ∧ γ t ≤ t₁ :=
  monotone_path_bounded γ_dipath
/-- The source of a directed path on I is `≤` than its target -/
lemma directed_path_source_le_target {t₀ t₁ : I} {γ : Path t₀ t₁} (γ_dipath : IsDipath γ) : t₀ ≤ t₁ :=
  monotone_path_source_le_target γ_dipath
end DirectedUnitInterval
end Lean4_directed_unit_interval
/-! Source module: Lean4.unit_interval_aux -/
section Lean4_unit_interval_aux
/-
  This file contains lemmas about
  * elements being contained in the unit interval.
  * relations between elements in the unit interval.
-/
open scoped unitInterval
namespace unitIAux
lemma zero_le (T : I) : ⟨0, unitInterval.zero_mem⟩ ≤ T := Subtype.coe_le_coe.mp T.2.1
lemma le_one (T : I) : T ≤ ⟨1, unitInterval.one_mem⟩:= Subtype.coe_le_coe.mp T.2.2
lemma double_pos_of_pos {T : I} (hT₀ : 0 < T) : 0 < (2 * T : ℝ) :=
  mul_pos two_pos hT₀
lemma double_sigma_pos_of_lt_one {T : I} (hT₁ : T < 1) : 0 < (2 * (1 - T) : ℝ) :=
  mul_pos two_pos (by {simp; exact hT₁})
lemma double_mem_I {t : I} (ht : ↑t ≤ (2⁻¹ : ℝ)) : 2 * (t : ℝ) ∈ I := by
  constructor
  exact mul_nonneg zero_le_two t.2.1
  calc 2 * (t : ℝ)
      _ ≤ 2 * 2⁻¹ := mul_le_mul_of_nonneg_left ht (by norm_num)
      _ = 1 := by norm_num
lemma double_sub_one_mem_I {t : I} (ht : (2⁻¹ : ℝ) ≤ ↑t) : 2 * (t : ℝ) - 1 ∈ I := by
  constructor
  calc 0 = 2 * (2⁻¹ : ℝ) - 1 := by norm_num
       _ ≤ 2 * ↑t - 1        := sub_le_sub_right (mul_le_mul_of_nonneg_left ht (by norm_num)) 1
  calc 2 * (t : ℝ) - 1
      _ ≤ 2 * 1 - 1 := sub_le_sub_right (mul_le_mul_of_nonneg_left t.2.2 (by norm_num)) 1
      _ = 1         := by norm_num
lemma interp_left_le_of_le (T : I) {a b : I} (hab : a ≤ b) : (σ T : ℝ) * ↑a + ↑T ≤ (σ T : ℝ) * ↑b + ↑T := by
  exact add_le_add_left
    (mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mp hab) (σ T).2.1) (T : ℝ)
section
noncomputable section
lemma half_mem_I : (2⁻¹ : ℝ) ∈ I :=
⟨by norm_num, by norm_num⟩
abbrev half_I : I := ⟨(2⁻¹ : ℝ), half_mem_I⟩
lemma has_T_half {t₀ t₁ : I} (γ : Path t₀ t₁) (ht₀ : ↑t₀ < (2⁻¹ : ℝ)) (ht₁ : ↑t₁ > (2⁻¹ : ℝ)) :
  ∃ (T : I),  0 < T ∧ T < 1 ∧ (γ T) = half_I := by
  have : γ.toFun 0 ≤ half_I := by rw [γ.source']; exact Subtype.coe_le_coe.mp (le_of_lt ht₀)
  have h₀ : ∃ (t : I), γ t ≤ half_I := ⟨0, this⟩
  have : half_I ≤ γ.toFun 1 := by rw [γ.target']; exact Subtype.coe_le_coe.mp (le_of_lt ht₁)
  have h₁ : ∃ (t : I), half_I ≤ γ t := ⟨1, this⟩
  have hy := Set.mem_range.mp (mem_range_of_exists_le_of_exists_ge γ.continuous_toFun h₀ h₁)
  cases' hy with T hT
  use T
  have hT₀ : 0 ≠ T := by
    rintro ⟨rfl⟩
    apply lt_irrefl (t₀ : ℝ)
    calc (t₀ : ℝ)
        _ < 2⁻¹       := ht₀
        _ = (γ 0 : ℝ) := Subtype.coe_inj.mpr hT.symm
        _ = ↑t₀       := Subtype.coe_inj.mpr γ.source'
  have hT₁ : T ≠ 1 := by
    rintro ⟨rfl⟩
    apply lt_irrefl (t₁ : ℝ)
    calc (t₁ : ℝ)
      _ = (γ 1 : ℝ) := Subtype.coe_inj.mpr γ.target'.symm
      _ = half_I    := Subtype.coe_inj.mpr hT
      _ < ↑t₁       := ht₁
  exact ⟨lt_iff_le_and_ne.mpr ⟨T.2.1, hT₀⟩, lt_iff_le_and_ne.mpr ⟨T.2.2, hT₁⟩, hT⟩
end
end
end unitIAux
end Lean4_unit_interval_aux
/-! Source module: Lean4.dipath -/
section Lean4_dipath
/-
  This file contains the definition of a dipath in a directed space:
  A path between two points paired with the proof that it is a dipath.
  The following dipath constructions are given:
  * refl : the constant dipath
  * trans : the concatenation of dipaths
  * map : the image of a dipath under a directed map
  * subparam : the monotonic subparametrization of a dipath
-/
noncomputable section
open DirectedMap Set
open scoped unitInterval
universe u
variable {X : Type u} [DirectedSpace X] {x y z : X}
/-- A dipath is a path together with a proof that that path "is a dipath" -/
structure Dipath (x y : X) extends Path x y :=
  (dipath_toPath : IsDipath toPath)
instance : Coe (Dipath x y) (Path x y) := ⟨fun γ => γ.toPath⟩
namespace Dipath
lemma directed (γ : Dipath x y) : DirectedMap.Directed γ.toContinuousMap :=
  fun _ _ _ φ_dipath => isDipath_reparam φ_dipath γ.dipath_toPath
def toDirectedMap (γ : Dipath x y) : D(I, X) where
  toContinuousMap := γ.toContinuousMap
  directed_toFun := Dipath.directed γ
instance Dipath.instFunLike : FunLike (Dipath x y) I X where
  coe := fun γ => γ.toContinuousMap
  coe_injective := fun γ γ' h => by
    obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := γ
    obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := γ'
    congr
instance Dipath.directedMapClass : DirectedMapClass (Dipath x y) I X where
  map_continuous := fun γ => γ.continuous
  map_directed := fun γ => directed γ
end Dipath
@[ext]
protected lemma Dipath.ext : ∀ {γ₁ γ₂ : Dipath x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂ := by
  rintro ⟨⟨⟨x, h10⟩, h11, h12⟩, h13⟩ ⟨⟨⟨y, h20⟩, h21, h22⟩, h23⟩ rfl
  rfl
namespace Dipath
def of_isDipath {γ : Path x y} (hγ :IsDipath γ) : Dipath x y := {
  toPath := γ,
  dipath_toPath := hγ,
}
/-- An directed map from I to a directed space can be turned into a dipath -/
def of_directedMap (f : D(I, X)) : Dipath (f 0) (f 1) := {
  toContinuousMap := f.toContinuousMap,
  source' := by simp,
  target' := by simp,
  dipath_toPath := DirectedUnitInterval.isDipath_of_isDipath_comp_id
    $ f.directed_toFun DirectedUnitInterval.IdentityPath DirectedUnitInterval.isDipath_identityPath
}
@[simp] lemma coe_mk (f : I → X) (h₀ h₁ h₂ h₃) : ⇑(mk ⟨⟨f, h₀⟩, h₁, h₂⟩ h₃ : Dipath x y) = f := rfl
variable (γ : Dipath x y)
@[continuity]
protected lemma continuous : Continuous γ :=
  γ.continuous_toFun
@[simp] protected lemma source : γ 0 = x :=
  γ.source'
@[simp] protected lemma target : γ 1 = y :=
  γ.target'
/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply : I → X :=
  γ
initialize_simps_projections Dipath (toPath_toContinuousMap_toFun → simps.apply, -toPath_toContinuousMap)
@[simp]
lemma coe_toContinuousMap : ⇑γ.toContinuousMap = γ := rfl
@[simp]
lemma coe_toDirectedMap : ⇑γ.toDirectedMap = γ := rfl
/-- Any function `φ : Π (a : α), Dipath (x a) (y a)` can be seen as a function `α × I → X`. -/
instance hasUncurryDipath {X α : Type*} [DirectedSpace X] {x y : α → X} :
  Function.HasUncurry (∀ a : α, Dipath (x a) (y a)) (α × I) X :=
⟨fun φ p => φ p.1 p.2⟩
/-! ### Properites about the range of dipaths -/
@[simp] lemma coe_range (γ : Dipath x y) : range γ = range γ.toPath := rfl
@[simp] lemma range_eq_image (γ : Dipath x y) : range γ = γ.extend '' I :=
  Set.ext (fun z =>
    ⟨fun ⟨t, ht⟩ => (Set.mem_image γ.extend I z).mpr ⟨t, t.2, by { simp; exact ht }⟩,
    fun ⟨t, t_mem_I, ht⟩ => ⟨⟨t, t_mem_I⟩, by {
      rw [ht.symm, Path.extend_extends γ.toPath t_mem_I]
      rfl
    }⟩⟩
  )
@[simp] lemma range_eq_image_I (γ : Dipath x y) : range γ = γ '' Icc 0 1 :=
  Set.ext (fun _ =>
    ⟨fun ⟨t, ht⟩ => (Set.mem_image γ (Icc 0 1) _).mpr ⟨t, t.2, ht⟩,
    fun ⟨t, t_mem_I, ht⟩ => ⟨⟨t, t_mem_I⟩, ht⟩⟩
  )
lemma image_extend_eq_image (γ : Dipath x y) (a b : I) : γ.extend '' Icc ↑a ↑b = γ '' Icc a b := by
  ext y
  constructor
  {
    rintro ⟨t, t_ab, ht⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨le_trans a.2.1 t_ab.1, le_trans t_ab.2 b.2.2⟩
    use ⟨t, htI⟩
    rw [←ht, Path.extend_extends γ.toPath htI]
    refine ⟨t_ab, rfl⟩
  }
  {
    rintro ⟨t, t_ab, ht⟩
    use t
    constructor
    exact t_ab
    have htI : (t : ℝ) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact le_trans a.2.1 (Subtype.coe_le_coe.mpr t_ab.1)
      · exact le_trans (Subtype.coe_le_coe.mpr t_ab.2) b.2.2
    rw [← ht]
    rw [Path.extend_apply γ.toPath htI]
    rfl
  }
/-! ### Reflexive dipaths -/
/-- The constant dipath from a point to itself -/
@[refl, simps!]
def refl (x : X) : Dipath x x where
  toPath := Path.refl x
  dipath_toPath := isDipath_constant x
@[simp] lemma refl_range {a : X} : range (Dipath.refl a) = {a} := Path.refl_range
/-! ### Concatenation of dipaths -/
/-- Directed paths can be concatenated -/
@[trans] def trans (γ : Dipath x y) (γ' : Dipath y z) : Dipath x z :=
{
  γ.toPath.trans γ'.toPath with
  dipath_toPath := isDipath_concat γ.dipath_toPath γ'.dipath_toPath
}
@[simp] lemma trans_to_path (γ : Dipath x y) (γ' : Dipath y z) :
  γ.toPath.trans γ'.toPath = (γ.trans γ').toPath := by
  ext t
  rfl
lemma trans_apply (γ : Dipath x y) (γ' : Dipath y z) (t : I) : (γ.trans γ') t =
  if h : (t : ℝ) ≤ 1/2 then
    γ ⟨2 * t, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨t.2.1, h⟩⟩
  else
    γ' ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ :=
Path.trans_apply (γ.toPath) (γ'.toPath) t
lemma trans_range (γ : Dipath x y) (γ' : Dipath y z) : range (γ.trans γ') = range γ ∪ range γ' :=
  Path.trans_range γ.toPath γ'.toPath
lemma trans_eval_at_half (γ : Dipath x y) (γ' : Dipath y z) :
    (γ.trans γ') (Fraction.ofPos two_pos) = y := by
  rw [Dipath.trans_apply]
  simp
/-! ### Mapping dipaths -/
/-- Image of a dipath from `x` to `y` by a directed map -/
def map (γ : Dipath x y) {Y : Type*} [DirectedSpace Y] (f : D(X, Y)) : Dipath (f x) (f y) :=
{
  γ.toPath.map f.continuous_toFun with
  dipath_toPath := f.directed_toFun γ.toPath γ.dipath_toPath,
}
@[simp] lemma map_coe (γ : Dipath x y) {Y : Type*} [DirectedSpace Y] (f : D(X, Y)) :
  (γ.map f : I → Y) = f ∘ γ :=
by { ext t; rfl }
@[simp] lemma map_trans (γ : Dipath x y) (γ' : Dipath y z) {Y : Type*} [DirectedSpace Y] (f : D(X, Y)) :
  (γ.trans γ').map f = (γ.map f).trans (γ'.map f) := by
  ext t
  rw [trans_apply, map_coe, Function.comp_apply, trans_apply]
  simp
  split_ifs <;> rfl
@[simp] lemma map_id (γ : Dipath x y) : γ.map (DirectedMap.id X) = γ := by { ext; rfl }
@[simp] lemma map_map (γ : Dipath x y) {Y : Type*} [DirectedSpace Y] {Z : Type*} [DirectedSpace Z]
  (f : D(X, Y)) (g : D(Y, Z)) : (γ.map f).map g = γ.map (g.comp f) := by { ext; rfl }
/-! ### Casting dipaths -/
/-- Casting a dipath from `x` to `y` to a dipath from `x'` to `y'` when `x' = x` and `y' = y` -/
def cast (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) : Dipath x' y' :=
{ toFun := γ,
  continuous_toFun := γ.continuous,
  dipath_toPath := isDipath_cast γ.toPath hx hy γ.dipath_toPath,
  source' := by simp [hx],
  target' := by simp [hy]
}
lemma cast_apply (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) (t : I):
  (γ.cast hx hy) t = γ t := rfl
@[simp] lemma trans_cast {X : Type*} [DirectedSpace X] {a₁ a₂ b₁ b₂ c₁ c₂ : X}
  (γ : Dipath a₂ b₂) (γ' : Dipath b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
  (γ.cast ha hb).trans (γ'.cast hb hc) = (γ.trans γ').cast ha hc := rfl
@[simp] lemma cast_coe (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) :
  (γ.cast hx hy : I → X) = γ := rfl
lemma cast_range (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) :
  range (γ.cast hx hy) = range γ := rfl
lemma cast_image (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) (a b : ℝ) :
  (γ.cast hx hy).extend '' Icc a b = γ.extend '' Icc a b := rfl
lemma dipath_of_directed_map_of_to_dimap (γ : Dipath x y) :
  Dipath.of_directedMap (γ.toDirectedMap) = γ.cast γ.source' γ.target' := by {ext t; rfl }
/-! ### Reparametrising a path -/
def subparam (γ : Dipath x y) (f : D(I, I)) : Dipath (γ (f 0)) (γ (f 1)) :=
{
  toFun := γ ∘ f
  continuous_toFun := by continuity
  source' := rfl
  target' := rfl
  dipath_toPath := by
      set p : Path (f 0) (f 1) :=
        { toFun := f,
          continuous_toFun := f.continuous_toFun,
          source' := rfl,
          target' := rfl
        }
      have p_mono : Monotone p := DirectedUnitInterval.monotone_of_directed f
      exact isDipath_reparam p_mono γ.dipath_toPath
}
lemma subparam_range (γ : Dipath x y) (f : D(I, I)) :
  range (γ.subparam f) ⊆ range γ := fun _ ⟨a, ha⟩ => ⟨f a, ha⟩
/--
Given a dipath `γ` and a dimap `f : I → I` where `f 0 = 0` and `f 1 = 1`, `γ.reparam f` is the
dipath defined by `γ ∘ f`.
-/
def reparam (γ : Dipath x y) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  Dipath x y :=
(subparam γ f).cast (hf₀.symm ▸ γ.source.symm) (hf₁.symm ▸ γ.target.symm)
@[simp]
lemma coe_to_fun (γ : Dipath x y) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  ⇑(γ.reparam f hf₀ hf₁) = γ ∘ f := rfl
@[simp]
lemma reparam_id (γ : Dipath x y) : γ.reparam (DirectedMap.id I) rfl rfl = γ :=
by { ext; rfl }
lemma range_reparam (γ : Dipath x y) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  range (γ.reparam f hf₀ hf₁) = range γ :=
Path.range_reparam γ.toPath f.continuous_toFun hf₀ hf₁
variable {Y : Type*} [DirectedSpace Y] {x₀ x₁ : X} {y₀ y₁ : Y}
/-- Two dipaths together form a dipath in the product space -/
def dipath_product (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath y₀ y₁) : Dipath (x₀, y₀) (x₁, y₁) where
  toPath := {
    toContinuousMap := ⟨fun t => (γ₁ t, γ₂ t), γ₁.continuous.prodMk γ₂.continuous⟩
    source' := by simp [γ₁.source', γ₂.source']
    target' := by simp [γ₁.target', γ₂.target']
  }
  dipath_toPath := by
      constructor
      · convert γ₁.dipath_toPath using 1 <;> ext t <;> rfl
      · convert γ₂.dipath_toPath using 1 <;> ext t <;> rfl
/-- Given a directed path in a product space, we can project it to its first coordinate to
obtain a directed path -/
def of_product_fst (γ : Dipath (x₀, y₀) (x₁, y₁)) : Dipath x₀ x₁ where
  toPath := γ.toPath.map continuous_fst
  dipath_toPath := γ.dipath_toPath.1
/-- Given a directed path in a product space, we can project it to its second coordinate to
obtain a directed path -/
def of_product_snd (γ : Dipath (x₀, y₀) (x₁, y₁)) : Dipath y₀ y₁ where
  toPath := γ.toPath.map continuous_snd
  dipath_toPath := γ.dipath_toPath.2
end Dipath
end
end Lean4_dipath
/-! Source module: Lean4.dTop -/
section Lean4_dTop
/-!
Bundled category of directed spaces. This follows the current Mathlib
`TopCat` structure instead of the removed `BundledHom` API.
-/
open DirectedMap
open CategoryTheory
universe u
structure dTopCat where
  /-- Underlying type. -/
  carrier : Type u
  /-- Topology and directed structure on the underlying type. -/
  [str : DirectedSpace carrier]
attribute [instance] dTopCat.str
namespace dTopCat
instance : CoeSort dTopCat (Type u) := ⟨dTopCat.carrier⟩
instance : Category dTopCat where
  Hom X Y := DirectedMap X Y
  id X := DirectedMap.id X
  comp f g := DirectedMap.comp g f
  id_comp f := DirectedMap.comp_id f
  comp_id f := DirectedMap.id_comp f
  assoc f g h := (DirectedMap.comp_assoc h g f).symm
instance concreteCategory : ConcreteCategory dTopCat (fun X Y => DirectedMap X Y) where
  hom f := f
  ofHom f := f
instance directedSpaceUnbundled (X : dTopCat) : DirectedSpace X := X.str
instance (X Y : dTopCat) : CoeFun (X ⟶ Y) (fun _ => X → Y) where
  coe f := f
lemma id_app (X : dTopCat.{u}) (x : ↑X) : (𝟙 X : X → X) x = x := rfl
lemma comp_app {X Y Z : dTopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g : X → Z) x = g (f x) := rfl
/-- Construct a bundled directed space. -/
def of (X : Type u) [DirectedSpace X] : dTopCat := ⟨X⟩
instance directedSpace_coe (X : dTopCat) : DirectedSpace X := X.str
@[reducible]
instance directedSpace_forget (X : dTopCat) : DirectedSpace <| (forget dTopCat).obj X := X.str
instance subspace_coe {X : dTopCat} : CoeTC (Set X) dTopCat := ⟨fun s => dTopCat.of s⟩
def DirectedSubtypeHom {X : dTopCat} (Y : Set X) : (dTopCat.of Y) ⟶ X :=
  DirectedSubtypeInclusion (fun s => s ∈ Y)
def DirectedSubsetHom {X : dTopCat} {Y₀ Y₁ : Set X} (h : Y₀ ⊆ Y₁) : (dTopCat.of Y₀) ⟶ Y₁ :=
  DirectedSubsetInclusion h
end dTopCat
end Lean4_dTop
/-! Source module: Lean4.interpolate -/
section Lean4_interpolate
/-
  This file contains definitions about interpolating points in the directed unit interval
  and contains conditions about when interpolating gives directed maps.
-/
open scoped unitInterval
universe u
section
lemma interp_mem_I (T a b : I) : (σ T : ℝ) * ↑a + ↑T * ↑b ∈ I := by
    constructor
    calc (0 : ℝ)
        _ = ↑(σ T) * 0 + ↑T * 0 := by simp
        _ ≤ ↑(σ T) * a + ↑T * 0 := add_le_add_left (mul_le_mul (le_refl (σ T : ℝ)) a.2.1 (le_refl 0) (σ T).2.1) (↑T * 0)
        _ ≤ ↑(σ T) * a + ↑T * b := add_le_add_right (mul_le_mul (le_refl ↑T) b.2.1 (le_refl 0) T.2.1) (↑(σ T) * ↑a)
    calc (σ T : ℝ) * ↑a + ↑T * ↑b
        _ ≤ ↑(σ T) * 1 + ↑T * ↑b  := add_le_add_left (mul_le_mul (le_refl (σ T : ℝ)) a.2.2 a.2.1 (σ T).2.1) (↑T * ↑b)
        _ ≤ ↑(σ T) * 1 + ↑T * 1   := add_le_add_right (mul_le_mul (le_refl ↑T) b.2.2 b.2.1 T.2.1) (↑(σ T) * 1)
        _ = 1                     := by simp
lemma interp_left_mem_I (T a : I) : (σ T : ℝ) * ↑a + ↑T ∈ I := by
  convert interp_mem_I T a 1
  simp
lemma interp_right_mem_I (T b : I) : (σ T : ℝ) + ↑T * ↑b ∈ I := by
  convert interp_mem_I T 1 b
  simp
lemma interp_const_le_of_le_of_le {a b T₀ T₁ : I} (hab : a ≤ b) (hT : T₀ ≤ T₁) :
  ((σ T₀ : ℝ) * ↑a + ↑T₀ * ↑b) ≤ (σ T₁ : ℝ) * ↑a + ↑T₁ * ↑b := by
  have h₁ : (T₀ : ℝ) * (b - a) ≤ T₁ * (b - a) := mul_le_mul_of_nonneg_right hT (sub_nonneg_of_le hab)
  calc (1 - T₀ : ℝ) * (a : ℝ) + (T₀ : ℝ) * (b : ℝ)
      _ = (a : ℝ) + ↑T₀ * (b - a)                        := by ring
      _ ≤ ↑a + ↑T₁ * (b - a)                             := add_le_add_right h₁ a
      _ = (1 - T₁ : ℝ) * (a : ℝ) + (T₁ : ℝ) * (b : ℝ)   := by ring
def interpolate_const (a b : I) : C(I, I) where
  toFun := fun t => ⟨_, interp_mem_I t a b⟩
def directed_interpolate_const {a b : I} (h : a ≤ b) : D(I, I) where
  toContinuousMap := interpolate_const a b
  directed_toFun := fun _ _ _ hγ _ _ hxy => interp_const_le_of_le_of_le h (hγ hxy)
variable (f g : C(I, I))
def interpolate : C(I × I, I) where
  toFun := fun t => ⟨(σ t.1 : ℝ) * (f t.2) + t.1 * (g t.2), interp_mem_I t.1 (f t.2) (g t.2)⟩
lemma interpolate_left : (interpolate f g).curry 0 = f := by
  ext
  simp [interpolate]
lemma interpolate_right : (interpolate f g).curry 1 = g := by
  ext
  simp [interpolate]
lemma interpolate_constant_apply (t v : I) (hf : f t = v) (hg : g t = v) :
    ∀ x, interpolate f g (x, t) = v := by
  intro x
  simp [interpolate, hf, hg]
  ring_nf
end
section
variable (f g : D(I, I))
lemma directed_interpolate (h : ∀ t, f t ≤ g t) :
    DirectedMap.Directed (interpolate f.toContinuousMap g.toContinuousMap) := by
  intros t₀ t₁ γ γ_dipath x y hxy
  let a₀ := (γ x).1
  let a₁ := (γ x).2
  let b₀ := (γ y).1
  let b₁ := (γ y).2
  have hfab : (f a₁ : ℝ) ≤ f b₁ := DirectedUnitInterval.monotone_of_directed f (γ_dipath.2 hxy)
  have hgab : (g a₁ : ℝ) ≤ g b₁ := DirectedUnitInterval.monotone_of_directed g (γ_dipath.2 hxy)
  have : 0 ≤ (g a₁ : ℝ) - (f a₁ : ℝ) := by simp [h]
  have h₁ : (a₀ : ℝ) * (g a₁ - f a₁) ≤ b₀ * (g a₁ - f a₁) := mul_le_mul_of_nonneg_right (γ_dipath.1 hxy) this
  apply Subtype.coe_le_coe.mp
  calc (interpolate f.toContinuousMap g.toContinuousMap (γ x) : ℝ)
      _  = (1 - a₀ : ℝ) * (f a₁ : ℝ) + (a₀ : ℝ) * (g a₁ : ℝ) := by rfl
      _  = ↑(f a₁) + ↑a₀ * (g a₁ - f a₁)                      := by ring
      _  ≤ ↑(f a₁) + ↑b₀ * (g a₁ - f a₁)                      := add_le_add_right h₁ ↑(f a₁)
      _  = (1 - b₀ : ℝ) * (f a₁ : ℝ) + (b₀ : ℝ) * (g a₁ : ℝ) := by ring
      _  ≤ (1 - b₀ : ℝ) * (f b₁ : ℝ) + (b₀ : ℝ) * (g a₁ : ℝ) := add_le_add_left (mul_le_mul_of_nonneg_left hfab (by unit_interval)) ((b₀ : ℝ) * (g a₁ : ℝ))
      _  ≤ (1 - b₀ : ℝ) * (f b₁ : ℝ) + (b₀ : ℝ) * (g b₁ : ℝ) := add_le_add_right (mul_le_mul_of_nonneg_left hgab (by unit_interval)) ((1 - b₀ : ℝ) * (f b₁ : ℝ))
      _  = (interpolate f.toContinuousMap g.toContinuousMap (γ y) : ℝ) := rfl
end
end Lean4_interpolate
/-! Source module: Lean4.SplitPath.split_path -/
section Lean4_SplitPath_split_path
/- This file contains definitions for splitting a path `γ : Path x y` at some point `T : I`
  yielding two different paths:
  * Its first part, from `x` to `γ T`, given by evaluating `γ` on `[0, T]`.
  * Its second part, from `γ T` to `y`, given by evaluating `γ` on `[T, 1]`.
-/
open scoped unitInterval
noncomputable section
universe u
variable {X : Type u} [DirectedSpace X] {x₀ x₁ : X}
namespace SplitPath
/-- The part of a path on the interval [0, T] -/
def FirstPart (γ : Path x₀ x₁) (T : I) : Path x₀ (γ T) where
  toFun := fun t => γ ⟨(T : ℝ) * ↑t, unitInterval.mul_mem T.2 t.2⟩
  source' := by simp [γ.source']
  target' := by simp
/-- The part of a path on the interval [T, 1] -/
def SecondPart (γ : Path x₀ x₁) (T : I) : Path (γ T) x₁ where
  toFun := fun t => γ ⟨(σ T : ℝ) * ↑t + ↑T, interp_left_mem_I T t⟩
  source' := by simp
  target' := by simp [γ.target']
/--
  The map needed to reparametrize the concatenation of the first and second part of a path
  back into the original pat
-/
def trans_reparam (T t : I) : ℝ :=
if (t : ℝ) ≤ (T : ℝ) then
  t / (2 * T)
else
  (1 + t - 2*T) / (2 * (1-T))
@[continuity]
lemma continuous_trans_reparam {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : Continuous (trans_reparam T) := by
  refine' continuous_if_le _ _ (Continuous.continuousOn _) (Continuous.continuousOn _) _
  · continuity
  · continuity
  · continuity
  · continuity
  intro x hx
  apply (div_eq_div_iff (ne_of_gt (unitIAux.double_pos_of_pos hT₀)) (ne_of_gt (unitIAux.double_sigma_pos_of_lt_one hT₁))).mpr
  simp [hx]
  ring
lemma trans_reparam_mem_I (t : I) {T : I} (hT₀ : 0 < T) (hT₁ : T < 1): trans_reparam T t ∈ I := by
  unfold trans_reparam
  split
  case isTrue h₀ =>
    constructor
    · exact div_nonneg t.2.1 (le_of_lt (unitIAux.double_pos_of_pos hT₀))
    · apply (div_le_one (unitIAux.double_pos_of_pos hT₀)).mpr
      have : 0 < (T : ℝ) := hT₀
      have : (T : ℝ) ≤ (2 * T : ℝ) := by linarith only [this]
      apply le_trans h₀ this
  case isFalse h₀ =>
    constructor
    · apply div_nonneg _ (le_of_lt (unitIAux.double_sigma_pos_of_lt_one hT₁))
      linarith [unitIAux.double_sigma_pos_of_lt_one hT₁]
    · exact (div_le_one (unitIAux.double_sigma_pos_of_lt_one hT₁)).mpr (by
      linarith only [unitInterval.le_one t])
lemma trans_reparam_zero (T : I) : trans_reparam T 0 = 0 := by
  unfold trans_reparam
  simp
  intro hT
  linarith [unitInterval.nonneg T]
lemma trans_reparam_one {T : I} (hT₁ : T < 1): trans_reparam T 1 = 1 := by
  unfold trans_reparam
  split_ifs
  case pos h =>
    exfalso
    exact lt_irrefl T (lt_of_lt_of_le hT₁ (Subtype.coe_le_coe.mp h))
  case neg h =>
    apply (div_eq_one_iff_eq _).mpr
    · show (1 : ℝ) + 1 - 2 * T = 2 * (1 - T)
      ring
    · simp
      have h₁ : T ≠ 1 := ne_of_lt hT₁
      exact fun h₂ => h₁ (Subtype.coe_inj.mp ((sub_eq_zero.mp h₂).symm))
lemma monotone_trans_reparam {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : Monotone (trans_reparam T) := by
  intro x y hxy
  unfold trans_reparam
  split_ifs with h₁ h₂
  · exact (div_le_div_iff_of_pos_right (unitIAux.double_pos_of_pos hT₀)).mpr (Subtype.coe_le_coe.mpr hxy)
  · apply (div_le_div_iff₀ (unitIAux.double_pos_of_pos hT₀) (unitIAux.double_sigma_pos_of_lt_one hT₁)).mpr
    have : 0 ≤ (T : ℝ) * (↑y - ↑T) := mul_nonneg T.2.1 (by linarith)
    calc (x : ℝ) * (2 * (1 - ↑T))
      _ ≤  ↑T * (2 * (1 - ↑T))                    := mul_le_mul_of_nonneg_right h₁ (le_of_lt (unitIAux.double_sigma_pos_of_lt_one hT₁))
      _ ≤  ↑T * (2 * (1 - ↑T)) + ↑T * (↑y - ↑T)   := le_add_of_nonneg_right (mul_nonneg T.2.1 (by linarith))
      _ ≤ (1 + ↑y - 2 * ↑T)  * (2 * ↑T)           := by linarith
  · linarith [Subtype.coe_le_coe.mpr hxy]
  · apply (div_le_div_iff_of_pos_right (unitIAux.double_sigma_pos_of_lt_one hT₁)).mpr
    linarith [Subtype.coe_le_coe.mpr hxy]
lemma first_trans_second_reparam_eq_self_aux (γ : Path x₀ x₁) (t : I) {T: I} (hT₀ : 0 < T) (hT₁ : T < 1) :
    γ t = ((FirstPart γ T).trans (SecondPart γ T)).reparam
    (fun t => ⟨trans_reparam T t, trans_reparam_mem_I t hT₀ hT₁⟩)
    (by continuity)
    (Subtype.ext $ trans_reparam_zero T) (Subtype.ext $ trans_reparam_one hT₁) t := by
  have hT_ne_zero : (T : ℝ) ≠ 0 := (lt_iff_le_and_ne.mp (Subtype.coe_lt_coe.mpr hT₀)).2.symm
  rw [Path.reparam]
  simp [Path.trans_apply, FirstPart, SecondPart, trans_reparam]
  split_ifs with h₁ h₂ h₂
  · congr
    apply Subtype.coe_inj.mp
    simp
    calc (t : ℝ)
      _ = t * 1 := (mul_one (t : ℝ)).symm
      _ = t * ((2 * T) / (2 * T)) := by rw [div_self (mul_ne_zero two_ne_zero hT_ne_zero)]
      _ = T * (2 * (t / (2 * T))) := by ring
  · exfalso
    have hT_lt_t : ↑T < ↑t := by
      simp at h₂
      calc (T : ℝ)
        _ = 1 * T                     := (one_mul (T : ℝ)).symm
        _ = (2⁻¹ * 2) * T             := by norm_num
        _ = 2⁻¹ * (2 * T)             := by ring
        _ < (t / (2 * T)) * (2 * T) := mul_lt_mul_of_pos_right h₂ (unitIAux.double_pos_of_pos hT₀)
        _ = t * ((2 * T) / (2 * T)) := by ring
        _ = t * 1                     := by rw [div_self (mul_ne_zero two_ne_zero hT_ne_zero)]
        _ = t                         := (mul_one (t : ℝ))
    exact not_le_of_gt hT_lt_t h₁
  · exfalso
    have : (1 + (t : ℝ) - 2 * ↑T) ≤ (1 - ↑T) := by
      rw [div_le_iff₀ (unitIAux.double_sigma_pos_of_lt_one hT₁)] at h₂
      simp at h₂
      simp [h₂]
    apply h₁ (Subtype.coe_le_coe.mp _)
    linarith
  · congr
    apply Subtype.coe_inj.mp
    simp
    calc (t : ℝ)
      _ = (1 + t - 2 * T) - 1 + 2 * T := by ring
      _ = (1 + t - 2 * T) * (2 * (1 - T)) / (2 * (1 - T)) - 1 + 2 * ↑T
            := by simp [mul_div_cancel_right₀ ((1 : ℝ) + t - 2 * T) (ne_of_gt (unitIAux.double_sigma_pos_of_lt_one hT₁))]
      _ = (1 - T) * (2 * ((1 + t - 2 * T) / (2 * (1 - T))) - 1) + T := by ring
lemma first_trans_second_reparam_eq_self (γ : Path x₀ x₁) {T: I} (hT₀ : 0 < T) (hT₁ : T < 1) :
    γ = ((FirstPart γ T).trans (SecondPart γ T)).reparam
    (fun t => ⟨trans_reparam T t, trans_reparam_mem_I t hT₀ hT₁⟩)
    (by continuity)
    (Subtype.ext $ trans_reparam_zero T) (Subtype.ext $ trans_reparam_one hT₁) := by
  ext t
  exact first_trans_second_reparam_eq_self_aux γ t hT₀ hT₁
end SplitPath
end
end Lean4_SplitPath_split_path
/-! Source module: Lean4.SplitPath.split_dipath -/
section Lean4_SplitPath_split_dipath
/- This file contains definitions for splitting a directed path `γ : Dipath x y` at some point
  `T : I` yielding two different directed paths:
  * Its first part, from `x` to `γ T`, given by evaluating `γ` on `[0, T]`.
  * Its second part, from `γ T` to `y`, given by evaluating `γ` on `[T, 1]`.
-/
noncomputable section
universe u
variable {X : Type u} [DirectedSpace X] {x₀ x₁ : X}
namespace SplitDipath
open SplitPath
open scoped unitInterval
lemma first_part_is_dipath {γ : Path x₀ x₁} (γ_dipath : IsDipath γ) (T : I) :
  IsDipath (FirstPart γ T) := by
  let φ : Path 0 T := {
    toFun := fun t => ⟨(T : ℝ) * (t : ℝ), unitInterval.mul_mem T.2 t.2⟩
    source' := by simp
    target' := by simp
  }
  have φ_mono : Monotone φ := fun x y hxy => by
    show (T : ℝ) * x ≤ T * y
    apply mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr hxy) T.2.1
  have : FirstPart γ T = (φ.map γ.continuous_toFun).cast γ.source.symm rfl := by { ext; rfl }
  rw [this]
  apply isDipath_cast _ γ.source.symm rfl
  exact isDipath_reparam φ_mono γ_dipath
lemma second_part_is_dipath {γ : Path x₀ x₁} (γ_dipath : IsDipath γ) (T : I) :
  IsDipath (SecondPart γ T) := by
  let φ : Path T 1 := {
    toFun := fun t => ⟨(σ T : ℝ) * (t : ℝ) + (T : ℝ), interp_left_mem_I T t⟩
    source' := by simp
    target' := by simp
  }
  have φ_mono : Monotone φ := fun x y hxy => by
    show (σ T : ℝ) * x + T ≤ (σ T : ℝ) * y + T
    have hmul : (σ T : ℝ) * x ≤ (σ T : ℝ) * y :=
      mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr hxy) (σ T).2.1
    linarith
  have : SecondPart γ T = ((φ.map γ.continuous_toFun).cast rfl γ.target.symm) := by { ext; rfl }
  rw [this]
  apply isDipath_cast _ rfl γ.target.symm
  exact isDipath_reparam φ_mono γ_dipath
def FirstPart (γ : Dipath x₀ x₁) (T : I) : Dipath x₀ (γ T) := {
  SplitPath.FirstPart (γ : Path x₀ x₁) T with
  dipath_toPath := first_part_is_dipath γ.dipath_toPath T
}
def SecondPart (γ : Dipath x₀ x₁) (T : I) : Dipath (γ T) x₁ := {
  SplitPath.SecondPart (γ : Path x₀ x₁) T with
  dipath_toPath := second_part_is_dipath γ.dipath_toPath T
}
@[simp]
lemma first_part_apply (γ : Dipath x₀ x₁) (T t : I) :
  (FirstPart γ T) t = γ ⟨ T* t, unitInterval.mul_mem T.2 t.2⟩ := rfl
@[simp]
lemma second_part_apply (γ : Dipath x₀ x₁) (T t : I) :
  (SecondPart γ T) t = γ ⟨(σ T : ℝ) * (t : ℝ) + (T : ℝ), interp_left_mem_I T t⟩ := rfl
def trans_reparam_map {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : D(I, I) :=
{
  toContinuousMap := ⟨fun t => ⟨trans_reparam T t, trans_reparam_mem_I t hT₀ hT₁⟩,
    Continuous.subtype_mk (continuous_trans_reparam hT₀ hT₁) _⟩,
  directed_toFun := DirectedUnitInterval.directed_of_monotone _ (monotone_trans_reparam hT₀ hT₁)
}
lemma trans_reparam_map_zero {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : trans_reparam_map hT₀ hT₁ 0 = 0 :=
  Subtype.ext (trans_reparam_zero T)
lemma trans_reparam_map_one {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : trans_reparam_map hT₀ hT₁ 1 = 1 :=
  Subtype.ext (trans_reparam_one hT₁)
lemma first_trans_second_reparam_eq_self (γ : Dipath x₀ x₁) {T: I} (hT₀ : 0 < T) (hT₁ : T < 1) :
  γ = ((FirstPart γ T).trans (SecondPart γ T)).reparam
    (trans_reparam_map hT₀ hT₁) (trans_reparam_map_zero _ _) (trans_reparam_map_one _ _) := by
  ext t
  exact first_trans_second_reparam_eq_self_aux (γ : Path x₀ x₁) t hT₀ hT₁
end SplitDipath
end
end Lean4_SplitPath_split_dipath
/-! Source module: Lean4.stretch_path -/
section Lean4_stretch_path
/-
  This file contains definitions about stretching a (directed) path in `I` in two ways:
    If its image is contained in `[0, 1/2]`, it can be stretched upwards
    If its image is contained in `[1/2, 1]`, it can be stretched downwards
  These cases can be determined by the endpoints of the directed path.
-/
open unitIAux
open scoped unitInterval
namespace Dipath
/-### Stretching a path that only lives in the first half of the unit interval upwards -/
lemma double_mem_I_of_bounded {t₀ t₁ : I} (t : I) (γ : Dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) : 2 * (γ t : ℝ) ∈ I :=
  double_mem_I $ le_trans (monotone_path_bounded γ.dipath_toPath t).2 (ht₁)
def stretch_up_path {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) : Path
  (⟨2 * ↑t₀, by { rw [←γ.source']; exact double_mem_I_of_bounded 0 γ ht₁ }⟩ : I)
  ⟨2 * ↑t₁, double_mem_I ht₁⟩ where
    toContinuousMap := ⟨fun t => ⟨2 * (γ t : ℝ), double_mem_I_of_bounded t γ ht₁⟩,
      Continuous.subtype_mk (continuous_const.mul (continuous_subtype_val.comp γ.continuous)) _⟩
    source' := by simp [γ.source']
    target' := by simp [γ.target']
lemma isDipath_stretch_up {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) :
  IsDipath (stretch_up_path γ ht₁) := by
  intros x y hxy
  unfold stretch_up_path
  simp
  exact γ.dipath_toPath hxy
def stretch_up {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) : Dipath
  (⟨2 * ↑t₀, by { rw [←γ.source']; exact double_mem_I_of_bounded 0 γ ht₁ }⟩ : I)
  ⟨2 * ↑t₁, double_mem_I ht₁⟩ where
    toPath := stretch_up_path γ ht₁
    dipath_toPath := isDipath_stretch_up γ ht₁
/-### Stretching a path that only lives in the second half of the unit interval downwards -/
lemma double_sub_one_mem_I_of_bounded {t₀ t₁ : I} (t : I) (γ : Dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀)
 : 2 * (γ t : ℝ) - 1 ∈ I :=
  double_sub_one_mem_I $ le_trans ht₀ (monotone_path_bounded γ.dipath_toPath t).1
def stretch_down_path {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀) : Path
  (⟨2 * ↑t₀ - 1, double_sub_one_mem_I ht₀⟩ : I)
  ⟨2 * ↑t₁ - 1, by { rw [←γ.target']; exact double_sub_one_mem_I_of_bounded 1 γ ht₀ }⟩ where
    toContinuousMap := ⟨fun t => ⟨2 * (γ t : ℝ) - 1, double_sub_one_mem_I_of_bounded t γ ht₀⟩,
      Continuous.subtype_mk
        ((continuous_const.mul (continuous_subtype_val.comp γ.continuous)).sub continuous_const) _⟩
    source' := by simp [γ.source']
    target' := by simp [γ.target']
lemma isDipath_stretch_down {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀) :
  IsDipath (stretch_down_path γ ht₀) := by
  intros x y hxy
  unfold stretch_down_path
  simp
  exact γ.dipath_toPath hxy
def stretch_down {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀) : Dipath
  (⟨2 * ↑t₀ - 1, double_sub_one_mem_I ht₀⟩ : I)
  ⟨2 * ↑t₁ - 1, by { rw [←γ.target']; exact double_sub_one_mem_I_of_bounded 1 γ ht₀ }⟩ where
    toPath := stretch_down_path γ ht₀
    dipath_toPath := isDipath_stretch_down γ ht₀
end Dipath
end Lean4_stretch_path
/-! Source module: Lean4.directed_homotopy -/
section Lean4_directed_homotopy
/-
  This file contains the definitions of three type of directed homotopies:
  * `Dihomotopy f g` : the type of homotopies between two directed maps `f g : D(X, Y)`.
  * `Dihomotopy_with f g P` : the type of homotopies between two directed maps `f g : D(X, Y)` satisfying `P : D(X, Y) → Prop` at all intermediate point `t : I`.
  * `Dihomotopy_rel f g S` : the type of homotopies between two directed maps `f g : D(X, Y)` that are fixed on all points of `S : set X`.
  The structure of this file is based on the undirected variant in Mathlib, found at:
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Homotopy/Basic.lean
-/
noncomputable section
namespace DirectedMap
open DirectedMap DirectedUnitInterval
open unitIAux
open scoped unitInterval
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [DirectedSpace X] [DirectedSpace Y] [DirectedSpace Z]
/-- `DirectedMap.Dihomotopy f₀ f₁` is the type of directed homotopies from `f₀` to `f₁`. -/
structure Dihomotopy (f₀ f₁ : DirectedMap X Y) extends D((I × X), Y) :=
  (map_zero_left : ∀ x, toFun (0, x) = f₀.toFun x)
  (map_one_left : ∀ x, toFun (1, x) = f₁.toFun x)
section
/-- `DirectedMap.DihomotopyLike F f₀ f₁` states that `F` is a type of homotopies between `f₀` and `f₁` -/
class DihomotopyLike {X Y : outParam (Type*)} [DirectedSpace X] [DirectedSpace Y]
    (F : Type*) (f₀ f₁ : outParam <| D(X, Y)) [FunLike F (I × X) Y]
    extends DirectedMapClass F (I × X) Y : Prop where
  map_zero_left (f : F) : ∀ x, f (0, x) = f₀ x
  map_one_left (f : F) : ∀x, f (1, x) = f₁ x
end
namespace Dihomotopy
section
variable {f₀ f₁ : D(X, Y)}
instance instFunLike : FunLike (Dihomotopy f₀ f₁) (I × X) Y where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr
instance : DihomotopyLike (Dihomotopy f₀ f₁) f₀ f₁ where
  map_continuous f := f.continuous_toFun
  map_directed f := f.directed_toFun
  map_zero_left f := f.map_zero_left
  map_one_left f := f.map_one_left
end
variable {f₀ f₁ : D(X, Y)}
@[ext] theorem ext {f g : Dihomotopy f₀ f₁} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h
/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.apply (F : Dihomotopy f₀ f₁) : I × X → Y := F
initialize_simps_projections Dihomotopy (toDirectedMap_toContinuousMap_toFun → apply, -toDirectedMap_toContinuousMap)
@[simp] lemma apply_zero (F : Dihomotopy f₀ f₁) (a : X) : F (0, a) = f₀ a := F.map_zero_left a
@[simp] lemma apply_one (F : Dihomotopy f₀ f₁) (a : X) : F (1, a) = f₁ a := F.map_one_left a
@[simp] lemma coe_to_continuous_map (F : Dihomotopy f₀ f₁) : ⇑F.toContinuousMap = F := rfl
@[simp] lemma coe_to_directed_map (F : Dihomotopy f₀ f₁) : ⇑F.toDirectedMap = F := rfl
/--
Currying a dihomotopy to a map fron `I` to `D(X, Y)`.
-/
def curry (F : Dihomotopy f₀ f₁) : I → D(X, Y) := by
  intro t
  exact DirectedMap.prod_const_fst ↑F t
@[simp]
lemma curry_apply (F : Dihomotopy f₀ f₁) (t : I) (x : X) : F.curry t x = F (t, x) := rfl
/--
Currying a dihomotopy to a map fron `X` to `D(I, Y)`.
-/
def curry_snd (F : Dihomotopy f₀ f₁) : X → D(I, Y) := by
  intro x
  exact DirectedMap.prod_const_snd ↑F x
@[simp]
lemma curry_snd_apply (F : Dihomotopy f₀ f₁) (x : X) (t : I) : F.curry_snd x t = F (t, x) := rfl
def hom_to_dihom (F : ContinuousMap.Homotopy (↑f₀ : C(X, Y)) ↑f₁) (HF : Directed (F : C(I × X, Y))) :
  Dihomotopy f₀ f₁ where
    toFun := F.toFun
    continuous_toFun := F.continuous_toFun
    directed_toFun := HF
    map_zero_left := F.map_zero_left
    map_one_left := F.map_one_left
def dihom_to_hom (F : Dihomotopy f₀ f₁) : ContinuousMap.Homotopy (f₀ : C(X, Y)) ↑f₁ where
  toFun := F.toFun
  continuous_toFun := F.continuous_toFun
  map_zero_left := F.map_zero_left
  map_one_left := F.map_one_left
instance coe_dihom_to_hom : Coe (Dihomotopy f₀ f₁) (ContinuousMap.Homotopy (f₀ : C(X, Y)) ↑f₁) :=
  ⟨fun F => F.dihom_to_hom⟩
section
/-! Evaluating dihomotopies at intermidiate points -/
/--
Evaluating a dipath homotopy at an intermediate point in the left coordinate, giving us a `dipath`.
-/
def eval_at_left {f g : D(I, X)} (F : Dihomotopy f g) (t : I) : Dipath (F (t, 0)) (F (t, 1)) where
  toContinuousMap := (F.curry t).toContinuousMap
  source' := by simp
  target' := by simp
  dipath_toPath := DirectedUnitInterval.isDipath_of_isDipath_comp_id
    $ (F.curry t).directed_toFun DirectedUnitInterval.IdentityPath DirectedUnitInterval.isDipath_identityPath
/--
Given a dihomotopy H: f ∼ g, get the dipath traced by the point `x` as it moves from
`f x` to `g x`
-/
def eval_at_right {X : Type*} {Y : Type*} [DirectedSpace X] [DirectedSpace Y] {f g : D(X, Y)}
  (H : DirectedMap.Dihomotopy f g) (x : X) : Dipath (f x) (g x) where
    toContinuousMap := ⟨fun t => H (t, x), H.continuous_toFun.comp (continuous_id.prodMk continuous_const)⟩
    source' := H.apply_zero x
    target' := H.apply_one x
    dipath_toPath := by
        convert H.directed_toFun { toFun := fun t => (t, x), source' := rfl, target' := rfl}
          ⟨DirectedUnitInterval.isDipath_identityPath, isDipath_constant _⟩ <;> simp
end
/--
Given a directed map `f`, we can define a `Dihomotopy f f` by `F (t, x) = f x`
-/
lemma directed_refl (f : D(X, Y)) : Directed (↑(ContinuousMap.Homotopy.refl (↑f : C(X, Y))) : C(I × X, Y)) :=
  fun _ _ γ γ_dipath => (f.directed_toFun (γ.map continuous_snd) (directed_snd.directed_toFun γ γ_dipath))
@[simps!]
def refl (f : D(X, Y)) : Dihomotopy f f := hom_to_dihom _ (directed_refl f)
instance : Inhabited (Dihomotopy (DirectedMap.id X) (DirectedMap.id X)) := ⟨Dihomotopy.refl _⟩
/- Note: there is no `Dihomotopy.symm`, as paths generally cannot be reversed -/
/- Auxiliary functions to prove that homotopy.trans is directed if the given homotopies are directed -/
section trans_aux
section trans_aux₁
open SplitPath SplitDipath
variable {t₀ t₁ : I} (γ : Dipath t₀ t₁) {T : I}
variable (hT : γ T = half_I)
def FirstPartStretch (ht₀ : (t₀ : ℝ) ≤ 2⁻¹) : Dipath (⟨2 * (t₀.1 : ℝ), double_mem_I ht₀⟩ : I) (1 : I) where
  toPath := (Dipath.stretch_up (FirstPart γ T)
      (by { convert le_refl (2⁻¹ : ℝ); simp [hT] })).toPath.cast (by simp) (by simp [hT])
  dipath_toPath := isDipath_cast _ _ _ <| Dipath.isDipath_stretch_up (FirstPart γ T)
    (by { convert le_refl (2⁻¹ : ℝ); simp [hT] })
def SecondPartStretch (ht₁ : 2⁻¹ ≤ (t₁ : ℝ)) : Dipath (0 : I) ⟨2 * (t₁.1 : ℝ) - 1, double_sub_one_mem_I ht₁⟩ where
  toPath := (Dipath.stretch_down (SecondPart γ T)
      (by { convert le_refl (2⁻¹ : ℝ); simp [hT] })).toPath.cast (by simp [hT]) (by simp)
  dipath_toPath := isDipath_cast _ _ _ <| Dipath.isDipath_stretch_down (SecondPart γ T)
    (by { convert le_refl (2⁻¹ : ℝ); simp [hT] })
end trans_aux₁
section trans_aux₂
variable {f₂ : D(X, Y)} (F : Dihomotopy f₀ f₁) (G: Dihomotopy f₁ f₂) (t : I) (x : X)
lemma trans_apply_half_left (ht: t = half_I) : (dihom_to_hom F).trans (dihom_to_hom G) (t, x) = F (1, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  have ht_coe : (t : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr ht
  have : (t : ℝ) ≤ 2⁻¹ := by linarith
  simp [this]
  simp [ht_coe]
lemma trans_apply_half_right (ht: t = half_I) : (dihom_to_hom F).trans (dihom_to_hom G) (t, x) = G (0, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  have ht_coe : (t : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr ht
  split_ifs <;> simp [ht_coe]
lemma trans_apply_left (t : I) (x : X) (ht : (t : ℝ) ≤ 2⁻¹) :
  (dihom_to_hom F).trans (dihom_to_hom G) (t, x) = F (⟨2 * t, double_mem_I ht⟩, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  simp [ht]
  rfl
lemma trans_apply_right (t : I) (x : X) (ht : 2⁻¹ ≤ (t : ℝ)) :
  (dihom_to_hom F).trans (dihom_to_hom G) (t, x) = G (⟨2 * t - 1, double_sub_one_mem_I ht⟩, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  simp [ht]
  split_ifs
  {
    have : (t : ℝ) = 2⁻¹ := by linarith
    simp [this]
  }
  rfl
end trans_aux₂
section trans_aux₃
variable {f₂ : D(X, Y)} (F : Dihomotopy f₀ f₁) (G: Dihomotopy f₁ f₂)
lemma trans_first_case {a₀ a₁ : I × X} {γ : Path a₀ a₁} (γ_dipath : IsDipath γ) (ht₁ : (a₁.1 : ℝ) ≤ 2⁻¹) :
  IsDipath (γ.map ((dihom_to_hom F).trans (dihom_to_hom G)).continuous_toFun) := by
  obtain ⟨t₀, x₀⟩ := a₀
  obtain ⟨t₁, x₁⟩ := a₁
  set Γ := (dihom_to_hom F).trans (dihom_to_hom G) with Γ_def
  set γ_as_dipath := Dipath.of_isDipath γ_dipath
  set γ₁ := γ_as_dipath.of_product_fst
  set γ₂ := γ_as_dipath.of_product_snd
  set p := Dipath.dipath_product (Dipath.stretch_up γ₁ ht₁) γ₂ with p_def
  set p' := p.map (↑F : D(I × X, Y)) with p'_def
  have h : ∀ (t : I) (x : X), (ht : (t : ℝ) ≤ 2⁻¹) → Γ (t, x) = F (⟨2 * (t : ℝ), double_mem_I ht⟩, x) := by
    intros t x ht
    rw [Γ_def]
    rw [ContinuousMap.Homotopy.trans_apply (dihom_to_hom F) (dihom_to_hom G) (t, x)]
    simp [ht]
    rfl
  have : (t₀ : ℝ) ≤ 2⁻¹ := le_trans (Subtype.coe_le_coe.mpr (directed_path_source_le_target γ_dipath.1)) ht₁
  convert (p'.cast (h t₀ x₀ this) (h t₁ x₁ ht₁)).dipath_toPath
  ext
  simp
  exact h _ _ (le_trans (directed_path_bounded γ_dipath.1 _).2 ht₁)
lemma trans_second_case {a₀ a₁ : I × X} {γ : Path a₀ a₁} (γ_dipath : IsDipath γ) (ht₀ : 2⁻¹ ≤ (a₀.1 : ℝ)) :
  IsDipath (γ.map ((dihom_to_hom F).trans (dihom_to_hom G)).continuous_toFun) := by
  obtain ⟨t₀, x₀⟩ := a₀
  obtain ⟨t₁, x₁⟩ := a₁
  set Γ := (dihom_to_hom F).trans (dihom_to_hom G) with Γ_def
  set γ_as_dipath := Dipath.of_isDipath γ_dipath
  set γ₁ := γ_as_dipath.of_product_fst
  set γ₂ := γ_as_dipath.of_product_snd
  set p := Dipath.dipath_product (Dipath.stretch_down γ₁ ht₀) γ₂ with p_def
  set p' := p.map (↑G : D(I × X, Y)) with p'_def
  have h : ∀ (t : I) (x : X), (ht : (2⁻¹ : ℝ) ≤ ↑t) →
    Γ (t, x) = G (⟨2 * (t : ℝ) - 1, double_sub_one_mem_I ht⟩, x) := by
    intros t x ht
    rw [Γ_def]
    rw [ContinuousMap.Homotopy.trans_apply (dihom_to_hom F) (dihom_to_hom G) (t, x)]
    split_ifs with ht'
    · simp at ht'
      have : ↑t = (2⁻¹ : ℝ) := by linarith
      simp [this]
    · rfl
  have : 2⁻¹ ≤ (t₁ : ℝ) := le_trans ht₀ (Subtype.coe_le_coe.mpr (directed_path_source_le_target γ₁.dipath_toPath))
  convert (p'.cast (h t₀ x₀ ht₀) (h t₁ x₁ this)).dipath_toPath
  ext
  simp
  exact h _ _ (le_trans ht₀ (directed_path_bounded γ_dipath.1 _).1)
end trans_aux₃
end trans_aux
/-
Given `Dihomotopy f₀ f₁` and `Dihomotopy f₁ f₂`, we can define a `Dihomotopy f₀ f₂` by putting the first
dihomotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₂ : D(X, Y)} (F : Dihomotopy f₀ f₁) (G: Dihomotopy f₁ f₂) : Dihomotopy f₀ f₂ := by
  set Fₕ := dihom_to_hom F
  set Gₕ := dihom_to_hom G
  set Γ := Fₕ.trans Gₕ
  apply hom_to_dihom Γ
  rintro ⟨t₀, x₀⟩ ⟨t₁, x₁⟩ γ γ_dipath
  set γ_as_dipath := Dipath.of_isDipath γ_dipath
  set γ₁ := γ_as_dipath.of_product_fst
  set γ₂ := γ_as_dipath.of_product_snd
  by_cases ht₁ : (↑t₁ : ℝ) ≤ 2⁻¹
  ·  -- The entire path falls in the domain of F
    exact trans_first_case F G γ_dipath ht₁
  by_cases ht₀ : (↑t₀ : ℝ) < 2⁻¹
  case neg
  · -- The entire path falls in the domain of G
    have ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀ := by linarith
    exact trans_second_case F G γ_dipath ht₀
  · -- Complicated
    push_neg at ht₁
    cases' has_T_half (γ.map continuous_fst) ht₀ ht₁ with T hT
    obtain ⟨hT₀, ⟨hT₁, hT_half⟩⟩ := hT
    /- Split γ into two parts (one with image in [0, 2⁻¹] × X, the other with image in [2⁻¹, 1] × X)-/
    set a₁ := SplitDipath.FirstPart γ_as_dipath T
    set a₂ := SplitDipath.SecondPart γ_as_dipath T
    /- Create two new paths, where the first coordinate is stretched and the second coordinate remains the same -/
    set p₁ := FirstPartStretch γ₁ hT_half (le_of_lt ht₀)
    set p₂ := SecondPartStretch γ₁ hT_half (le_of_lt ht₁)
    set p₁' := SplitDipath.FirstPart γ₂ T
    set p₂' := SplitDipath.SecondPart γ₂ T
    set q₁ := (Dipath.dipath_product p₁ p₁').map F.toDirectedMap
    set q₂ := (Dipath.dipath_product p₂ p₂').map G.toDirectedMap
    set φ := SplitDipath.trans_reparam_map hT₀ hT₁
    have φ₀ : φ 0 = 0 := Subtype.ext (SplitPath.trans_reparam_zero T)
    have φ₁ : φ 1 = 1 := Subtype.ext (SplitPath.trans_reparam_one hT₁)
    have hγT_eq_half : ((γ T).1 : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr hT_half
    have hγT_le_half : ((γ T).1 : ℝ) ≤ 2⁻¹ := le_of_eq hγT_eq_half
    set r₁ := q₁.cast (trans_apply_left F G t₀ x₀ (le_of_lt ht₀)) (trans_apply_half_left F G (γ T).1 (γ T).2 hT_half)
    set r₂ := q₂.cast (trans_apply_half_right F G (γ T).1 (γ T).2 hT_half) (trans_apply_right F G t₁ x₁ (le_of_lt ht₁))
    convert ((r₁.trans r₂).reparam φ φ₀ φ₁).dipath_toPath
    ext t
    have hr₁a₁ : r₁.toPath = a₁.toPath.map Γ.continuous_toFun := by
      ext x
      have h₀ : ((a₁ x).1 : ℝ) ≤ 2⁻¹ := le_trans (directed_path_bounded a₁.dipath_toPath.1 _).2 hγT_le_half
      have : (1/2 : ℝ) = 2⁻¹ := by norm_num
      calc r₁ x
        _ = F (⟨2 * ((a₁ x).1 : ℝ), double_mem_I h₀⟩, (a₁ x).2) := rfl
        _ = if h : ((a₁ x).1 : ℝ) ≤ 1/2
            then F (⟨2 * ((a₁ x).1 : ℝ), by { simp at h; exact double_mem_I h }⟩, (a₁ x).2)
            else G (⟨2 * ((a₁ x).1 : ℝ) - 1, by { simp at h; exact double_sub_one_mem_I (le_of_lt h) }⟩, (a₁ x).2)
                  := by { simp only [h₀, this]; simp }
        _ = if h : ((a₁ x).1 : ℝ) ≤ 1/2
            then Fₕ (⟨2 * ((a₁ x).1 : ℝ), by { simp at h; exact double_mem_I h }⟩, (a₁ x).2)
            else Gₕ (⟨2 * ((a₁ x).1 : ℝ) - 1, by { simp at h; exact double_sub_one_mem_I (le_of_lt h) }⟩, (a₁ x).2)
                  := rfl
        _ = (Fₕ.trans Gₕ) (a₁ x) := (ContinuousMap.Homotopy.trans_apply Fₕ Gₕ (a₁ x)).symm
        _ = Γ (a₁ x) := rfl
        _ = (a₁.toPath.map Γ.continuous_toFun) x := rfl
    have hr₂a₂ : r₂.toPath = a₂.toPath.map Γ.continuous_toFun := by
      ext x
      have : 2⁻¹ ≤ ((a₂ x).1 : ℝ) := by
        calc (2⁻¹ : ℝ)
            _ = ↑(γ T).1 := Subtype.coe_inj.mpr hT_half.symm
            _ ≤ ↑(a₂ x).1 := (directed_path_bounded a₂.dipath_toPath.1 _).1
      calc r₂.toPath x
        _ = G (⟨2 * ((a₂ x).1 : ℝ) - 1, double_sub_one_mem_I this⟩, (a₂ x).2) := rfl
        _ = if h : ((a₂ x).1 : ℝ) ≤ 1/2
                then F (⟨2 * ((a₂ x).1 : ℝ), by { simp at h; exact double_mem_I h }⟩, (a₂ x).2)
                else G (⟨2 * ((a₂ x).1 : ℝ) - 1,  by { simp at h; exact double_sub_one_mem_I (le_of_lt h) }⟩, (a₂ x).2)
              := by
                split_ifs with h
                · have : ((a₂ x).1 : ℝ) ≤ 2⁻¹ := by convert h using 1; norm_num
                  have ha₂x : ((a₂ x).1 : ℝ) = 2⁻¹ := by linarith
                  have : G (0, _) = F (1, _) := Eq.trans (G.map_zero_left (a₂ x).2) (F.map_one_left (a₂ x).2).symm
                  convert this <;> rw [ha₂x] <;> norm_num
                · rfl
        _ = if h : ((a₂ x).1 : ℝ) ≤ 1/2
                then Fₕ (⟨2 * ((a₂ x).1 : ℝ), by { simp at h; exact double_mem_I h }⟩, (a₂ x).2)
                else Gₕ (⟨2 * ((a₂ x).1 : ℝ) - 1, by { simp at h; exact double_sub_one_mem_I (le_of_lt h) }⟩, (a₂ x).2)
              := rfl
        _ = (Fₕ.trans Gₕ) (a₂ x) := (ContinuousMap.Homotopy.trans_apply Fₕ Gₕ (a₂ x)).symm
        _ = Γ (a₂ x) := rfl
        _ = (a₂.toPath.map Γ.continuous_toFun) x := rfl
    calc (Γ ∘ γ) t
        _ = Γ (γ t) := rfl
        _ = Γ (((a₁.trans a₂).reparam φ φ₀ φ₁) t) := by { rw [←SplitDipath.first_trans_second_reparam_eq_self γ_as_dipath hT₀ hT₁]; rfl }
        _ = ((a₁.trans a₂).toPath.map Γ.continuous_toFun).reparam φ φ.continuous_toFun φ₀ φ₁ t := by rfl
        _ = ((a₁.toPath.trans a₂.toPath).map Γ.continuous_toFun).reparam φ φ.continuous_toFun φ₀ φ₁ t := by rfl
        _ = ((a₁.toPath.map Γ.continuous_toFun).trans (a₂.toPath.map Γ.continuous_toFun)).reparam φ φ.continuous_toFun φ₀ φ₁ t
                                                                          := by rw [Path.map_trans a₁.toPath a₂.toPath (Γ.continuous_toFun)]
        _ = (r₁.toPath.trans r₂.toPath).reparam φ φ.continuous_toFun φ₀ φ₁ t := by rw [hr₁a₁, hr₂a₂]; rfl
        _ = (r₁.trans r₂).reparam φ φ₀ φ₁ t := rfl
lemma trans_apply {f₀ f₁ f₂ : D(X, Y)} (F : Dihomotopy f₀ f₁) (G : Dihomotopy f₁ f₂) (x : I × X) :
  (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) := by
  have : ((dihom_to_hom F).trans (dihom_to_hom G)) x = (F.trans G) x := rfl
  rw [←this]
  exact ContinuousMap.Homotopy.trans_apply _ _ x
/--
Casting a `Dihomotopy f₀ f₁` to a `Dihomotopy g₀ g₁` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps]
def cast {f₀ f₁ g₀ g₁ : D(X, Y)} (F : Dihomotopy f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
  Dihomotopy g₀ g₁ where
    toFun := F
    directed_toFun := F.directed_toFun
    map_zero_left := by simp [←h₀]
    map_one_left := by simp [←h₁]
/--
If we have a `Dihomotopy f₀ f₁` and a `Dihomotopy g₀ g₁`, then we can compose them and get a
`Dihomotopy (g₀.comp f₀) (g₁.comp f₁)`.
-/
@[simps!]
def hcomp {f₀ f₁ : D(X, Y)} {g₀ g₁ : D(Y, Z)} (F : Dihomotopy f₀ f₁) (G : Dihomotopy g₀ g₁) :
  Dihomotopy (g₀.comp f₀) (g₁.comp f₁) := by
  set Fₕ := dihom_to_hom F
  set Gₕ := dihom_to_hom G
  exact hom_to_dihom (Gₕ.comp Fₕ) (G.comp (directed_fst.prod_map_mk (F : D(I × X, Y)))).directed_toFun
end Dihomotopy
/--
  Given directed maps `f₀` and `f₁`, we say `f₀` and `f₁` are PreDihomotopic if there exists a
  `Dihomotopy f₀ f₁`.
-/
def PreDihomotopic (f₀ f₁ : D(X, Y)) : Prop := Nonempty (Dihomotopy f₀ f₁)
/--
  Given directed maps `f₀` and `f₁`, we say `f₀` and `f₁` are Dihomotopic if there
  is a chain of PreDihomotopic maps leading from `f₀` to `f₁`.
  In other words, Dihomotopic is the equivalence relation generated by PreDihomotopic.
-/
def Dihomotopic (f₀ f₁ : D(X, Y)) : Prop := (Relation.EqvGen PreDihomotopic) f₀ f₁
namespace Dihomotopic
lemma equivalence : Equivalence (@Dihomotopic X Y _ _) := by apply Relation.EqvGen.is_equivalence
end Dihomotopic
/--
The type of dihomotopies between `f₀ f₁ : D(X, Y)`, where the intermediate maps satisfy the predicate
`P : D(X, Y) → Prop`
-/
structure DihomotopyWith (f₀ f₁ : D(X, Y)) (P : D(X, Y) → Prop) extends Dihomotopy f₀ f₁ :=
(
  prop' : ∀ (t : I), P (toDirectedMap.prod_const_fst t)
)
namespace DihomotopyWith
section
variable {f₀ f₁ : D(X, Y)} {P : D(X, Y) → Prop}
instance instFunLike : FunLike (DihomotopyWith f₀ f₁ P) (I × X) Y where
  coe F := ⇑F.toDihomotopy
  coe_injective := by
    rintro ⟨⟨⟨⟨F, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨G, _⟩, _⟩, _⟩, _⟩ h
    congr
instance : DihomotopyLike (DihomotopyWith f₀ f₁ P) f₀ f₁ where
  map_continuous F := F.continuous_toFun
  map_directed F := F.directed_toFun
  map_zero_left F := F.map_zero_left
  map_one_left F := F.map_one_left
theorem coeFn_injective : @Function.Injective (DihomotopyWith f₀ f₁ P) (I × X → Y) (⇑) :=
  DFunLike.coe_injective
@[ext]
lemma ext {F G : DihomotopyWith f₀ f₁ P} (h : ∀ x, F x = G x) : F = G :=
coeFn_injective $ funext h
/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.apply (F : DihomotopyWith f₀ f₁ P) : I × X → Y := F
initialize_simps_projections DihomotopyWith (toDihomotopy_toDirectedMap_toContinuousMap_toFun → apply,
    -toDihomotopy_toDirectedMap_toContinuousMap)
@[continuity]
protected lemma continuous (F : DihomotopyWith f₀ f₁ P) : Continuous F := F.continuous_toFun
@[simp]
lemma apply_zero (F : DihomotopyWith f₀ f₁ P) (x : X) : F (0, x) = f₀ x := F.map_zero_left x
@[simp]
lemma apply_one (F : DihomotopyWith f₀ f₁ P) (x : X) : F (1, x) = f₁ x := F.map_one_left x
@[simp]
lemma coe_to_continuous_map (F : DihomotopyWith f₀ f₁ P) : ⇑F.toContinuousMap = F := rfl
@[simp]
lemma coe_to_dihomotopy (F : DihomotopyWith f₀ f₁ P) : ⇑F.toDihomotopy = F := rfl
lemma prop (F : DihomotopyWith f₀ f₁ P) (t : I) : P (F.toDihomotopy.curry t) := F.prop' t
end
variable {P : D(X, Y) → Prop}
/--
Given a directed map `f`, and a proof `h : P f`, we can define a `DihomotopyWith f f P` by `F (t, x) = f x`
-/
@[simps!]
def refl (f : D(X, Y)) (hf : P f) : DihomotopyWith f f P := {
  Dihomotopy.refl f with
  prop' := by
    intro t
    convert hf
    apply DirectedMap.ext
    intro x
    rfl
}
instance : Inhabited (DihomotopyWith (DirectedMap.id X) (DirectedMap.id X) (fun _ => True)) :=
  ⟨DihomotopyWith.refl _ trivial⟩
/--
Given `DihomotopyWith f₀ f₁ P` and `DihomotopyWith f₁ f₂ P`, we can define a `DihomotopyWith f₀ f₂ P`
by putting the first dihomotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : D(X, Y)} (F : DihomotopyWith f₀ f₁ P) (G : DihomotopyWith f₁ f₂ P) :
  DihomotopyWith f₀ f₂ P :=
{
  F.toDihomotopy.trans G.toDihomotopy with
  prop' := fun t => by
    simp only [Dihomotopy.trans]
    change P ⟨⟨fun _ => ite ((t : ℝ) ≤ _) _ _, _⟩, _⟩
    split
    case isTrue h =>
      have : ((t : ℝ) ≤ 2⁻¹) := by { simp at h; exact h }
      convert F.prop' ⟨2 * (t : ℝ), double_mem_I this⟩
      all_goals
        rename_i x
        change (F.toDihomotopy.dihom_to_hom.extend (2 * (t : ℝ))) x =
          F.toDihomotopy.dihom_to_hom (⟨2 * (t : ℝ), double_mem_I this⟩, x)
        rw [←ContinuousMap.Homotopy.extend_apply_coe
          F.toDihomotopy.dihom_to_hom ⟨2 * (t : ℝ), double_mem_I this⟩ x]
    case isFalse h =>
      have : (2⁻¹ ≤ (t : ℝ)) := by { simp at h; linarith }
      convert G.prop' ⟨2 * (t : ℝ) - 1, double_sub_one_mem_I this⟩
      all_goals
        rename_i x
        change (G.toDihomotopy.dihom_to_hom.extend (2 * (t : ℝ) - 1)) x =
          G.toDihomotopy.dihom_to_hom (⟨2 * (t : ℝ) - 1, double_sub_one_mem_I this⟩, x)
        rw [←ContinuousMap.Homotopy.extend_apply_coe
          G.toDihomotopy.dihom_to_hom ⟨2 * (t : ℝ) - 1, double_sub_one_mem_I this⟩ x]
}
lemma trans_apply {f₀ f₁ f₂ : D(X, Y)} (F : DihomotopyWith f₀ f₁ P) (G : DihomotopyWith f₁ f₂ P)
  (x : I × X) : (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
Dihomotopy.trans_apply _ _ _
/--
Casting a `DihomotopyWith f₀ f₁ P` to a `DihomotopyWith g₀ g₁ P` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
def cast {f₀ f₁ g₀ g₁ : D(X, Y)} (F : DihomotopyWith f₀ f₁ P) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
  DihomotopyWith g₀ g₁ P :=
{
  F.toDihomotopy.cast h₀ h₁ with
  prop' := F.prop,
}
end DihomotopyWith
/--
Given directed maps `f₀` and `f₁`, we say `f₀` and `f₁` are pre_dihomotopic with respect to the
predicate `P` if there exists a `DihomotopyWith f₀ f₁ P`.
-/
def PreDihomotopicWith (P : D(X, Y) → Prop) (f₀ f₁ : D(X, Y)): Prop :=
  Nonempty (DihomotopyWith f₀ f₁ P)
/--
`DihomotopicWith` is the equivalence relation generated by `PreDihomotopicWith`.
-/
def DihomotopicWith (P : D(X, Y) → Prop) (f₀ f₁ : D(X, Y)) : Prop := Relation.EqvGen (PreDihomotopicWith P) f₀ f₁
/--
A `DihomotopyRel f₀ f₁ S` is a dihomotopy between `f₀` and `f₁` which is fixed on the points in `S`.
-/
abbrev DihomotopyRel (f₀ f₁ : D(X, Y)) (S : Set X) :=
  DihomotopyWith f₀ f₁ (fun f => ∀ x ∈ S, f x = f₀ x)
namespace DihomotopyRel
section
variable {f₀ f₁ : D(X, Y)} {S : Set X}
lemma eq_fst (F : DihomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₀ x :=
  F.prop t x hx
lemma eq_snd (F : DihomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₁ x := by
  rw [F.eq_fst t hx, ← F.eq_fst 1 hx, F.apply_one]
lemma fst_eq_snd (F : DihomotopyRel f₀ f₁ S) {x : X} (hx : x ∈ S) : f₀ x = f₁ x :=
  F.eq_fst 0 hx ▸ F.eq_snd 0 hx
end
variable {f₀ f₁ f₂ : D(X, Y)} {S : Set X}
/--
Given a map `f : D(X, Y)` and a set `S`, we can define a `DihomotopyRel f f S` by setting
`F (t, x) = f x` for all `t`. This is defined using `DihomotopyWith.refl`, but with the proof
filled in.
-/
@[simps!]
def refl (f : D(X, Y)) (S : Set X) : DihomotopyRel f f S :=
DihomotopyWith.refl f (fun _ _ => rfl)
/--
Given `DihomotopyRel f₀ f₁ S` and `DihomotopyRel f₁ f₂ S`, we can define a `DihomotopyRel f₀ f₂ S`
by putting the first dihomotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : DihomotopyRel f₀ f₁ S) (G : DihomotopyRel f₁ f₂ S) : DihomotopyRel f₀ f₂ S :=
{
  Dihomotopy.trans F.toDihomotopy G.toDihomotopy with
  prop' := fun t => by
    intros x hx
    simp only [Dihomotopy.trans]
    change (⟨⟨fun _ => ite ((t : ℝ) ≤ _) _ _, _⟩, _⟩ : D(X, Y)) x = f₀ x
    split_ifs with h
    · have : ((t : ℝ) ≤ 2⁻¹) := by { simp at h; exact h }
      set t' : I := ⟨2 * (t : ℝ), double_mem_I this⟩
      convert F.eq_fst t' hx
      change ((F.toDihomotopy.dihom_to_hom.extend) (2 * t : ℝ)) x = F.toDihomotopy.dihom_to_hom (⟨2 * (t : ℝ), _⟩, x)
      rw [←ContinuousMap.Homotopy.extend_apply_coe F.toDihomotopy.dihom_to_hom _ x]
    · have : (2⁻¹ ≤ (t : ℝ)) := by { simp at h; linarith }
      set t' : I := ⟨2 * (t : ℝ) - 1, double_sub_one_mem_I this⟩
      convert (G.eq_fst t' hx).trans (F.fst_eq_snd hx).symm
      change ((G.toDihomotopy.dihom_to_hom.extend) (2 * (t : ℝ) - 1)) x = G.toDihomotopy.dihom_to_hom (⟨2 * (t : ℝ) - 1, _⟩, x)
      rw [←ContinuousMap.Homotopy.extend_apply_coe G.toDihomotopy.dihom_to_hom _ x]
}
lemma trans_apply (F : DihomotopyRel f₀ f₁ S) (G : DihomotopyRel f₁ f₂ S)
  (x : I × X) : (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
Dihomotopy.trans_apply _ _ _
/--
Casting a `DihomotopyRel f₀ f₁ S` to a `DihomotopyRel g₀ g₁ S` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
def cast {f₀ f₁ g₀ g₁ : D(X, Y)} (F : DihomotopyRel f₀ f₁ S) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
  DihomotopyRel g₀ g₁ S :=
{
  Dihomotopy.cast F.toDihomotopy h₀ h₁ with
  prop' := fun t x hx => by { simpa [←h₀, ←h₁] using F.prop t x hx }
}
end DihomotopyRel
/--
Given directed maps `f₀` and `f₁`, we say `f₀` and `f₁` are PreDihomotopic relative to a set `S` if
there exists a `DihomotopyRel f₀ f₁ S`.
-/
def PreDihomotopicRel (S : Set X) (f₀ f₁ : D(X, Y)) : Prop :=
Nonempty (DihomotopyRel f₀ f₁ S)
/--
`DihomotopicRel` is the equivalence relation generated by `PreDihomotopicRel`.
-/
def DihomotopicRel (S : Set X) (f₀ f₁ : D(X, Y)) : Prop := Relation.EqvGen (PreDihomotopicRel S) f₀ f₁
namespace DihomotopicRel
variable {S : Set X}
lemma equivalence : Equivalence (fun f g : D(X, Y) => DihomotopicRel S f g) := by apply Relation.EqvGen.is_equivalence
end DihomotopicRel
end DirectedMap
end
end Lean4_directed_homotopy
/-! Source module: Lean4.trans_refl -/
section Lean4_trans_refl
/-
  Auxiliary lemmas for the refl_trans and trans_refl definitions in directed_path_homotopy.lean.
  These two are definitions are dihomotopies related to a `p : Dipath x₀ x₁`:
    refl_trans : from `(refl x₀).trans p` to `p`
    trans_refl : from `p` to `p.trans (refl x₁)`
  Those for trans_refl can be based on the auxiliary lemmas found in algebraic_topology.fundamental_groupoid.basic.
  They use symmetry for refl_trans which is not possible in the directed case, so we have to define them manually.
-/
open DirectedSpace DirectedMap
open scoped unitInterval
universe u v
variable {X : Type u} {Y : Type v}
variable [DirectedSpace X] [DirectedSpace Y]
variable {x₀ x₁ : X}
noncomputable section
namespace Dipath
namespace Dihomotopy
open Path.Homotopy
section TransRefl
lemma directed_transReflReparamAux : DirectedMap.Directed
    ({ toFun := fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩,
       continuous_toFun := Continuous.subtype_mk continuous_transReflReparamAux _} : C(I, I)) := by
  apply DirectedUnitInterval.directed_of_monotone _
  intros x y hxy
  unfold transReflReparamAux
  simp
  have : (x : ℝ) ≤ (y : ℝ) := hxy
  split_ifs with h₁ h₂
  · linarith
  · calc 2 * (x : ℝ)
      _ ≤ 2 * 2⁻¹ := (mul_le_mul_iff_of_pos_left (by norm_num)).mpr h₁
      _ = 1       := by simp
  · linarith
  · linarith
def TransReflReparamAuxMap : D(I, I) where
  toContinuousMap := ⟨fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩,
    Continuous.subtype_mk continuous_transReflReparamAux _⟩
  directed_toFun := directed_transReflReparamAux
lemma trans_refl_reparam_dipath (p : Dipath x₀ x₁) : p.trans (Dipath.refl x₁) =
    p.reparam TransReflReparamAuxMap (Subtype.ext transReflReparamAux_zero)
      (Subtype.ext transReflReparamAux_one) := by
  ext t
  have : (p.trans (Dipath.refl x₁)) t = p.toPath.trans (Path.refl x₁) t := rfl
  rw [this, Path.Homotopy.trans_refl_reparam p.toPath]
  rfl
end TransRefl
section ReflTrans
/-- Auxilliary function for `ReflTransReparam` -/
def ReflTransReparamAux (t : I) : ℝ :=
if (t : ℝ) ≤ 1/2 then
  0
else
  2 * t - 1
@[continuity]
lemma continuous_ReflTransReparamAux : Continuous ReflTransReparamAux := by
  refine' continuous_if_le _ _ (Continuous.continuousOn _) (Continuous.continuousOn _) _ <;>
  [continuity; continuity; continuity; continuity; skip]
  intros x hx
  norm_num [hx]
lemma reflTransReparamAux_mem_I (t : I) : ReflTransReparamAux t ∈ I := by
  unfold ReflTransReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]
lemma reflTransReparamAux_zero : ReflTransReparamAux 0 = 0 :=
by norm_num [ReflTransReparamAux]
lemma reflTransReparamAux_one : ReflTransReparamAux 1 = 1 :=
by norm_num [ReflTransReparamAux]
lemma directed_ReflTransReparamAux : DirectedMap.Directed
    ({ toFun := fun t => ⟨ReflTransReparamAux t, reflTransReparamAux_mem_I t⟩,
       continuous_toFun := Continuous.subtype_mk continuous_ReflTransReparamAux _} : C(I, I)) := by
  apply DirectedUnitInterval.directed_of_monotone _
  intros x y hxy
  unfold ReflTransReparamAux
  simp
  have : (x : ℝ) ≤ (y : ℝ) := hxy
  split_ifs with h₁ h₂
  · linarith
  · calc (0 : ℝ)
      _ = (2 : ℝ) * (2⁻¹ : ℝ) - (1 : ℝ) := by norm_num
      _ ≤ 2 * (y : ℝ) - 1 := le_of_lt $ sub_lt_sub_right ((mul_lt_mul_iff_of_pos_left (by norm_num)).mpr (lt_of_not_ge h₂)) 1
  · linarith
  · linarith
def ReflTransReparamAuxMap : D(I, I) where
  toContinuousMap := ⟨fun t => ⟨ReflTransReparamAux t, reflTransReparamAux_mem_I t⟩,
    Continuous.subtype_mk continuous_ReflTransReparamAux _⟩
  directed_toFun := directed_ReflTransReparamAux
lemma refl_trans_reparam (p : Path x₀ x₁) :
    (Path.refl x₀).trans p =
      p.reparam (fun t => ⟨ReflTransReparamAux t, reflTransReparamAux_mem_I t⟩) (by continuity)
        (Subtype.ext reflTransReparamAux_zero) (Subtype.ext reflTransReparamAux_one) := by
  ext
  unfold ReflTransReparamAux
  simp [Path.trans_apply, not_le, coe_to_fun, Function.comp_apply]
  split_ifs
  · simp
  · simp
  · rfl
  · rfl
lemma refl_trans_reparam_dipath (p : Dipath x₀ x₁) : (Dipath.refl x₀).trans p =
    p.reparam ReflTransReparamAuxMap
      (Subtype.ext reflTransReparamAux_zero) (Subtype.ext reflTransReparamAux_one) := by
  ext t
  have : ((Dipath.refl x₀).trans p) t =  (Path.refl x₀).trans p.toPath t := rfl
  rw [this, refl_trans_reparam p.toPath]
  rfl
end ReflTrans
end Dihomotopy
end Dipath
end
end Lean4_trans_refl
/-! Source module: Lean4.directed_path_homotopy -/
section Lean4_directed_path_homotopy
/-
  This file contains the definition of a directed path homotopy, or `Dipath.Dihomotopy`:
  It is a dihomotopy between two paths that keeps the endpoints fixed.
  We prove a few constructions and define the equivalence relation `Dihomtopic` between two paths.
  We show that this relation is closed under reparametrizations, and that concatenation and directed maps respect it.
  Much of the structure of this file is based on the undirected version:
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Homotopy/Path.lean
-/
universe u v
open unitIAux
open DirectedUnitInterval
open scoped unitInterval
variable {X : Type u} {Y : Type v}
variable [DirectedSpace X] [DirectedSpace Y]
variable {x y z : X}
noncomputable section
namespace Dipath
/--
The type of dihomotopies between two directed paths.
-/
abbrev Dihomotopy (p₀ p₁ : Dipath x y) :=
  DirectedMap.DihomotopyRel p₀.toDirectedMap p₁.toDirectedMap {0, 1}
namespace Dihomotopy
section
variable {p₀ p₁ : Dipath x y}
lemma coeFn_injective : @Function.Injective (Dihomotopy p₀ p₁) (I × I → X) (⇑) :=
  DFunLike.coe_injective
@[simp]
lemma source (F : Dihomotopy p₀ p₁) (t : I) : F (t, 0) = x := by
  calc F (t, 0)
    _ = p₀ 0 := DirectedMap.DihomotopyRel.eq_fst _ _ (.inl rfl)
    _ = x := p₀.source
@[simp]
lemma target (F : Dihomotopy p₀ p₁) (t : I) : F (t, 1) = y := by
  calc F (t, 1)
    _ = p₀ 1 := DirectedMap.DihomotopyRel.eq_fst _ _ (.inr rfl)
    _ = y := p₀.target
/-- A `F : Dihomotopy ↑p₁ ↑p₂` between two dipaths `p₁ p₂ : Dipath y z` can be coerced into a dihomotopy,
  if it is directed -/
def hom_to_dihom (F : Path.Homotopy p₀.toPath p₁.toPath)
    (HF : DirectedMap.Directed F.toContinuousMap) : Dihomotopy p₀ p₁ where
  toFun := F.toFun
  continuous_toFun := F.continuous_toFun
  directed_toFun := HF
  map_zero_left := F.map_zero_left
  map_one_left := F.map_one_left
  prop' := F.prop'
/-- A Dihomotopy `F` between two Dipaths `p₁ p₂` can be coerced into a Homotopy between `p₀.toPath`
 and `p₁.toPath`-/
def dihom_to_hom (F : Dihomotopy p₀ p₁) : Path.Homotopy p₀.toPath p₁.toPath where
  toFun := F.toFun
  continuous_toFun := F.continuous_toFun
  map_zero_left := F.map_zero_left
  map_one_left := F.map_one_left
  prop' := F.prop'
instance coe_dihom_to_hom : Coe (Dihomotopy p₀ p₁) (Path.Homotopy p₀.toPath p₁.toPath) :=
  ⟨fun F => F.dihom_to_hom⟩
/--
Evaluating a dipath homotopy at an intermediate point, giving us a `Dipath`.
-/
def eval (F : Dihomotopy p₀ p₁) (t : I) : Dipath x y where
  toPath := {
    toContinuousMap := (F.toDihomotopy.curry t).toContinuousMap
    source' := F.source t
    target' := F.target t
  }
  dipath_toPath := DirectedUnitInterval.isDipath_of_isDipath_comp_id
    $ (F.toDihomotopy.curry t).directed_toFun DirectedUnitInterval.IdentityPath
      DirectedUnitInterval.isDipath_identityPath
@[simp]
lemma coe_eval (F : Dihomotopy p₀ p₁) (t : I) :
  (⇑(F.eval t) : I → X)  = ⇑(F.toDihomotopy.curry t) := rfl
@[simp]
lemma eval_zero (F : Dihomotopy p₀ p₁) : F.eval 0 = p₀ := by
  ext t
  change F.toDihomotopy (0, t) = p₀ t
  exact F.toDihomotopy.apply_zero t
@[simp]
lemma eval_one (F : Dihomotopy p₀ p₁) : F.eval 1 = p₁ := by
  ext t
  change F.toDihomotopy (1, t) = p₁ t
  exact F.toDihomotopy.apply_one t
end
section
variable {p₀ p₁ p₂ : Dipath x y}
/--
Given a dipath `p`, we can define a `Dihomotopy p p` by `F (t, x) = p x`
-/
@[simps!]
def refl (p : Dipath x y) : Dihomotopy p p :=
  DirectedMap.DihomotopyRel.refl p.toDirectedMap {0, 1}
/--
Given `Dihomotopy p₀ p₁` and `Dihomotopy p₁ p₂`, we can define a `Dihomotopy p₀ p₂` by putting the first
dihomotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : Dihomotopy p₀ p₁) (G : Dihomotopy p₁ p₂) : Dihomotopy p₀ p₂ :=
  DirectedMap.DihomotopyRel.trans F G
lemma trans_apply (F : Dihomotopy p₀ p₁) (G : Dihomotopy p₁ p₂) (x : I × I) :
  (F.trans G) x =
    if h : (x.1 : ℝ) ≤ 1/2 then
      F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨x.1.2.1, h⟩⟩, x.2)
    else
      G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
DirectedMap.DihomotopyRel.trans_apply _ _ _
/--
Casting a `Dihomotopy p₀ p₁` to a `Dihomotopy q₀ q₁` where `p₀ = q₀` and `p₁ = q₁`.
-/
-- @[simps]
def cast {p₀ p₁ q₀ q₁ : Dipath x y} (F : Dihomotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁) :
    Dihomotopy q₀ q₁ :=
  DirectedMap.DihomotopyRel.cast F (congr_arg _ h₀) (congr_arg _ h₁)
end
section
variable {p₀ q₀ : Dipath x y} {p₁ q₁ : Dipath y z}
section hcomp_aux
variable (F : Dihomotopy p₀ q₀) (G: Dihomotopy p₁ q₁) (s t : I) (ht: t = half_I)
lemma hcomp_apply_half_left (ht: t = half_I) :
    (dihom_to_hom F).hcomp (dihom_to_hom G) (s, t) = F (s, 1) := by
  rw [Path.Homotopy.hcomp_apply]
  have ht_coe : (t : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr ht
  have : (t : ℝ) ≤ 2⁻¹ := by linarith
  simp [this, ht_coe]
lemma hcomp_apply_half_right (ht: t = half_I) :
    (dihom_to_hom F).hcomp (dihom_to_hom G) (s, t) = G (s, 0) := by
  rw [Path.Homotopy.hcomp_apply]
  have ht_coe : (t : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr ht
  split_ifs <;> simp [ht_coe]
lemma hcomp_apply_left (ht : (t : ℝ) ≤ 2⁻¹) :
    (dihom_to_hom F).hcomp (dihom_to_hom G) (s, t) = F (s, ⟨2 * t, double_mem_I ht⟩) := by
  rw [Path.Homotopy.hcomp_apply]
  simp [ht]
  rfl
lemma hcomp_apply_right (ht : 2⁻¹ ≤ (t : ℝ)) :
    (dihom_to_hom F).hcomp (dihom_to_hom G) (s, t) = G (s, ⟨2 * t - 1, double_sub_one_mem_I ht⟩) := by
  rw [Path.Homotopy.hcomp_apply]
  simp [ht]
  split_ifs
  · have : (t : ℝ) = 2⁻¹ := by linarith
    simp [this]
  · rfl
lemma hcomp_first_case (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁) {a₀ a₁ : I × I} {γ : Path a₀ a₁}
  (γ_dipath : IsDipath γ) (ht₁ : (a₁.2 : ℝ) ≤ 2⁻¹) :
    IsDipath (γ.map ((dihom_to_hom F).hcomp (dihom_to_hom G)).continuous_toFun) := by
  obtain ⟨s₀, t₀⟩ := a₀
  obtain ⟨s₁, t₁⟩ := a₁
  set Γ := (dihom_to_hom F).hcomp (dihom_to_hom G)
  set γ_as_dipath := Dipath.of_isDipath γ_dipath
  set γ₁ := γ_as_dipath.of_product_fst
  set γ₂ := γ_as_dipath.of_product_snd
  set p := Dipath.dipath_product γ₁ (Dipath.stretch_up γ₂ ht₁)
  set p' := p.map (F.toDirectedMap)
  have h : ∀ (s t : I), (h : (t : ℝ) ≤ 2⁻¹) → Γ (s, t) = F (s, ⟨2 * (t : ℝ), double_mem_I h⟩) := by
    intros s t ht
    rw [Path.Homotopy.hcomp_apply (dihom_to_hom F) (dihom_to_hom G) (s, t)]
    simp [ht]
    rfl
  have ht₀ : (t₀ : ℝ) ≤ 2⁻¹ :=
    le_trans (Subtype.coe_le_coe.mpr (directed_path_source_le_target γ_dipath.2)) ht₁
  convert (p'.cast (h s₀ t₀ ht₀) (h s₁ t₁ ht₁)).dipath_toPath
  ext
  simp
  exact h _ _ (le_trans (directed_path_bounded γ_dipath.2 _).2 ht₁)
lemma hcomp_second_case (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁) {a₀ a₁ : I × I}
  {γ : Path a₀ a₁} (γ_dipath : IsDipath γ) (ht₀ : 2⁻¹ ≤ (a₀.2 : ℝ)) :
    IsDipath (γ.map ((dihom_to_hom F).hcomp (dihom_to_hom G)).continuous_toFun) := by
  obtain ⟨s₀, t₀⟩ := a₀
  obtain ⟨s₁, t₁⟩ := a₁
  set Γ := (dihom_to_hom F).hcomp (dihom_to_hom G)
  set γ_as_dipath := Dipath.of_isDipath γ_dipath
  set γ₁ := γ_as_dipath.of_product_fst
  set γ₂ := γ_as_dipath.of_product_snd
  set p := Dipath.dipath_product γ₁ (Dipath.stretch_down γ₂ ht₀)
  set p' := p.map G.toDirectedMap
  have h : ∀ (s t : I), (h : (2⁻¹ : ℝ) ≤ ↑t) →
    Γ (s, t) = G (s, ⟨2 * (t : ℝ) - 1, double_sub_one_mem_I h⟩) := by
    intros s t ht
    rw [Path.Homotopy.hcomp_apply (dihom_to_hom F) (dihom_to_hom G) (s, t)]
    split_ifs with ht'
    · simp at ht'
      have : ↑t = (2⁻¹ : ℝ) := by linarith
      simp [this]
    · rfl
  have ht₁ : 2⁻¹ ≤ (t₁ : ℝ) := le_trans ht₀ (Subtype.coe_le_coe.mpr (directed_path_source_le_target γ_dipath.2))
  convert (p'.cast (h s₀ t₀ ht₀) (h s₁ t₁ ht₁)).dipath_toPath
  ext x
  simp
  exact h (γ x).1 (γ x).2 (le_trans ht₀ (directed_path_bounded γ_dipath.2 _).1)
end hcomp_aux
/--
Suppose `p₀` and `q₀` are dipaths from `x` to `y`, `p₁` and `q₁` are dipaths from `y` to `z`.
Furthermore, suppose `F : Dihomotopy p₀ q₀` and `G : Dihomotopy p₁ q₁`. Then we can define a dihomotopy
from `p₀.trans p₁` to `q₀.trans q₁`.
-/
def hcomp (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁) :
    Dihomotopy (p₀.trans p₁) (q₀.trans q₁) := by
  set Fₕ := dihom_to_hom F
  set Gₕ := dihom_to_hom G
  set Γ := Fₕ.hcomp Gₕ
  have : DirectedMap.Directed Γ.toContinuousMap := by
    rintro ⟨s₀, t₀⟩ ⟨s₁, t₁⟩ γ γ_dipath
    set γ_as_dipath := Dipath.of_isDipath γ_dipath
    set γ₁ := γ_as_dipath.of_product_fst
    set γ₂ := γ_as_dipath.of_product_snd
    by_cases ht₁ : (↑t₁ : ℝ) ≤ 2⁻¹
    case pos => exact hcomp_first_case F G γ_dipath ht₁
    by_cases ht₀ : (↑t₀ : ℝ) < 2⁻¹
    case neg => exact hcomp_second_case F G γ_dipath (by linarith)
    -- Complicated
    push_neg at ht₁
    cases' has_T_half (γ.map continuous_snd) ht₀ ht₁ with T hT
    obtain ⟨hT₀, ⟨hT₁, hT_half⟩⟩ := hT
    /- Split γ into two parts (one with image in I × [0, 2⁻¹], the other with image in I × [2⁻¹, 1])-/
    set a₁ := SplitDipath.FirstPart γ_as_dipath T
    set a₂ := SplitDipath.SecondPart γ_as_dipath T
    /- Create two new paths, where the first coordinate is stretched and the second coordinate remains the same -/
    set p₁ := SplitDipath.FirstPart γ₁ T
    set p₂ := SplitDipath.SecondPart γ₁ T
    set p₁' := DirectedMap.Dihomotopy.FirstPartStretch γ₂ hT_half (le_of_lt ht₀)
    set p₂' := DirectedMap.Dihomotopy.SecondPartStretch γ₂ hT_half (le_of_lt ht₁)
    set q₁ := (Dipath.dipath_product p₁ p₁').map F.toDirectedMap
    set q₂ := (Dipath.dipath_product p₂ p₂').map G.toDirectedMap
    set φ := SplitDipath.trans_reparam_map hT₀ hT₁
    have φ₀ : φ 0 = 0 := Subtype.ext $ SplitPath.trans_reparam_zero T
    have φ₁ : φ 1 = 1 := Subtype.ext $ SplitPath.trans_reparam_one hT₁
    have hγT_eq_half : ((γ T).2 : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr hT_half
    have hγT_le_half : ((γ T).2 : ℝ) ≤ 2⁻¹ := le_of_eq hγT_eq_half
    set r₁ := q₁.cast (hcomp_apply_left F G s₀ t₀ (le_of_lt ht₀)) (hcomp_apply_half_left F G (γ T).1 (γ T).2 hT_half)
    set r₂ := q₂.cast (hcomp_apply_half_right F G (γ T).1 (γ T).2 hT_half) (hcomp_apply_right F G s₁ t₁ (le_of_lt ht₁))
    convert ((r₁.trans r₂).reparam φ φ₀ φ₁).dipath_toPath
    ext t
    have hr₁a₁ : r₁.toPath = a₁.toPath.map Γ.continuous_toFun := by
      ext x
      have this : ((a₁ x).2 : ℝ) ≤ 2⁻¹ := le_trans (directed_path_bounded a₁.dipath_toPath.2 _).2 hγT_le_half
      calc r₁ x
        _ = F ((a₁ x).1, ⟨2 * ((a₁ x).2 : ℝ), double_mem_I this⟩)
              := rfl
        _ = if h : ((a₁ x).2 : ℝ) ≤ 1/2
                then F ((a₁ x).1, ⟨2 * ((a₁ x).2 : ℝ), double_mem_I this⟩)
                else G ((a₁ x).1, ⟨2 * ((a₁ x).2 : ℝ) - 1, by { apply double_sub_one_mem_I (le_of_lt _); convert h; norm_num }⟩)
              := by apply Eq.symm; apply dif_pos; convert this using 1; norm_num
        _ = if h : ((a₁ x).2 : ℝ) ≤ 1/2
                then Fₕ.eval (a₁ x).1 ⟨2 * ((a₁ x).2 : ℝ), double_mem_I this⟩
                else Gₕ.eval (a₁ x).1 ⟨2 * ((a₁ x).2 : ℝ) - 1, by { apply double_sub_one_mem_I (le_of_lt _); convert h; norm_num }⟩
              := rfl
        _ = (Fₕ.hcomp Gₕ) (a₁ x)
              := (Path.Homotopy.hcomp_apply Fₕ Gₕ (a₁ x)).symm
        _ = Γ (a₁ x)
              := rfl
        _ = (a₁.toPath.map Γ.continuous_toFun) x
              := rfl
    have hr₂a₂ : r₂.toPath = a₂.toPath.map Γ.continuous_toFun := by
      ext x
      have : 2⁻¹ ≤ ((a₂ x).2 : ℝ) := by
        calc (2⁻¹ : ℝ)
          _ = ↑(γ T).2   := Subtype.coe_inj.mpr hT_half.symm
          _ ≤  ↑(a₂ x).2 := (directed_path_bounded a₂.dipath_toPath.2 _).1
      calc r₂.toPath x
        _ = G ((a₂ x).1, ⟨2 * ((a₂ x).2 : ℝ) - 1, double_sub_one_mem_I this⟩)
              := rfl
        _ = if h : ((a₂ x).2 : ℝ) ≤ 1/2
                then F ((a₂ x).1, ⟨2 * ((a₂ x).2 : ℝ), by { apply double_mem_I; convert h using 1; norm_num }⟩)
                else G ((a₂ x).1, ⟨2 * ((a₂ x).2 : ℝ) - 1,  by { apply double_sub_one_mem_I (le_of_lt _); convert h using 1; norm_num }⟩)
              := by
                split_ifs with h
                · have : ((a₂ x).2 : ℝ) ≤ 2⁻¹ := by convert h using 1; norm_num
                  have ha₂x : ((a₂ x).2 : ℝ) = 2⁻¹ := by linarith
                  have : G (_, 0) = F (_, 1) := Eq.trans (G.source (a₂ x).1) (F.target (a₂ x).1).symm
                  convert this <;> rw [ha₂x] <;> norm_num
                · rfl
        _ = if h : ((a₂ x).2 : ℝ) ≤ 1/2
                then Fₕ.eval (a₂ x).1 ⟨2 * ((a₂ x).2 : ℝ), by { apply double_mem_I; convert h using 1; norm_num }⟩
                else Gₕ.eval (a₂ x).1 ⟨2 * ((a₂ x).2 : ℝ) - 1, by { apply double_sub_one_mem_I (le_of_lt _); convert h using 1; norm_num }⟩
              := rfl
        _ = (Fₕ.hcomp Gₕ) (a₂ x)
              := (Path.Homotopy.hcomp_apply Fₕ Gₕ (a₂ x)).symm
        _ = Γ (a₂ x)
              := rfl
        _ = (a₂.toPath.map Γ.continuous_toFun) x
              := rfl
    calc (Γ ∘ γ) t
      _ = Γ (γ t)
            := rfl
      _ = Γ (((a₁.trans a₂).reparam φ φ₀ φ₁) t)
            := by rw [←SplitDipath.first_trans_second_reparam_eq_self γ_as_dipath hT₀ hT₁]; rfl
      _ = ((a₁.trans a₂).toPath.map Γ.continuous_toFun).reparam φ φ.continuous_toFun φ₀ φ₁ t
            := rfl
      _ = ((a₁.toPath.trans a₂.toPath).map Γ.continuous_toFun).reparam φ φ.continuous_toFun φ₀ φ₁ t
            := rfl
      _ = ((a₁.toPath.map Γ.continuous_toFun).trans (a₂.toPath.map Γ.continuous_toFun)).reparam φ φ.continuous_toFun φ₀ φ₁ t
            := by rw [Path.map_trans a₁.toPath a₂.toPath (Γ.continuous_toFun)]
      _ = (r₁.toPath.trans r₂.toPath).reparam φ φ.continuous_toFun φ₀ φ₁ t
            := by rw [hr₁a₁, hr₂a₂]; rfl
      _ = (r₁.trans r₂).reparam φ φ₀ φ₁ t
            := rfl
  exact hom_to_dihom Γ this
lemma hcomp_apply (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁) (x : I × I) :
    F.hcomp G x =
      if h : (x.2 : ℝ) ≤ 1/2 then
        F.eval x.1 ⟨2 * x.2, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨x.2.2.1, h⟩⟩
      else
        G.eval x.1 ⟨2 * x.2 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.2.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> exact Path.extend_extends _ _
lemma hcomp_half (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁) (t : I) :
    F.hcomp G (t, ⟨1/2, by norm_num, by norm_num⟩) = y :=
  show ite _ _ _ = _ by norm_num
end
/--
Suppose `p` is a dipath, and `f g : D(I, I)` two monotonic subparametrizations. If `f` is dominated by `g`,
i.e. `∀ t, f t ≤ g t`, then we obtain a dihomotopy between the two subparametrization of `p` as
the interpolation between the two becomes directed.
-/
def reparam (p : Dipath x y) (f : D(I, I)) (g : D(I, I)) (hf_le_g : ∀ (t : I), f t ≤ g t)
  (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) (hg₀ : g 0 = 0) (hg₁ : g 1 = 1) :
    Dihomotopy (p.reparam f hf₀ hf₁) (p.reparam g hg₀ hg₁) where
  toFun := p.comp (interpolate f.toContinuousMap g.toContinuousMap)
  map_zero_left := fun x => by { unfold interpolate; norm_num; rfl }
  map_one_left := fun x => by { unfold interpolate; norm_num; rfl }
  prop' := fun t x hx => by
    simp
    cases' hx with hx hx
    · have : g 0 = f 0 := hg₀.trans (hf₀.symm)
      rw [hx]
      calc (p ((interpolate f.toContinuousMap g.toContinuousMap) (t, 0)))
        _ = p (f 0) := by rw [interpolate_constant_apply f.toContinuousMap g.toContinuousMap 0 (f 0) rfl this t]
    · have : g 1 = f 1 := hg₁.trans (hf₁.symm)
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      calc (p ((interpolate f.toContinuousMap g.toContinuousMap) (t, 1)))
        _ = p (f 1) := by rw [interpolate_constant_apply f.toContinuousMap g.toContinuousMap 1 (f 1) rfl this t]
  directed_toFun := fun t₀ t₁ γ γ_dipath =>
    (p.toDirectedMap).directed_toFun (γ.map _) (directed_interpolate f g hf_le_g γ γ_dipath)
/--
For any `p : Dipath x y`, there is a dihomotopy from `p` to `p.trans (Dipath.refl y)`.
-/
def trans_refl (p : Dipath x y) : Dihomotopy p (p.trans (Dipath.refl y)) := by
  set f : D(I, I) := DirectedMap.id I
  set g : D(I, I) := TransReflReparamAuxMap
  have hf_le_g : ∀ (t : I), f t ≤ g t := by
    intro t
    apply Subtype.coe_le_coe.mp
    dsimp [f, g, TransReflReparamAuxMap, Path.Homotopy.transReflReparamAux]
    show (t : ℝ) ≤ ite ((t : ℝ) ≤ 1 / 2) ((2 : ℝ) * (t : ℝ)) 1
    split_ifs
    · have : 0 ≤ (t : ℝ) := t.2.1
      linarith
    · exact t.2.2
  convert reparam p f g hf_le_g (rfl) (rfl)
    (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
    (Subtype.ext Path.Homotopy.transReflReparamAux_one)
  · ext t
    rfl
  · exact trans_refl_reparam_dipath p
/--
For any `p : Dipath x y`, there is a dihomotopy from `(Dipath.refl x).trans p` to `p`.
-/
def refl_trans (p : Dipath x y) : Dihomotopy ((Dipath.refl x).trans p) p := by
  set f : D(I, I) := ReflTransReparamAuxMap
  set g : D(I, I) := DirectedMap.id I
  have hf_le_g : ∀ (t : I), f t ≤ g t := fun t => by
    apply Subtype.coe_le_coe.mp
    dsimp [f, g, ReflTransReparamAuxMap, ReflTransReparamAux]
    show ite ((t : ℝ) ≤ 1 / 2) 0 ((2 : ℝ) * (t : ℝ) - 1) ≤ (t : ℝ)
    split_ifs
    · exact t.2.1
    · linarith [t.2.2]
  convert reparam p f g hf_le_g (Subtype.ext reflTransReparamAux_zero)
    (Subtype.ext reflTransReparamAux_one) (rfl) (rfl)
  · exact refl_trans_reparam_dipath p
  · ext t
    rfl
/--
For any `p : Dipath x y`, there is a homotopy from `(Dipath.refl x).trans p` to `q.trans (Dipath.refl y)`,
where `q` is any directed reparametrization of `p`.
-/
def refl_trans_to_reparam_trans_refl (p : Dipath x y) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Dihomotopy ((Dipath.refl x).trans p) ((p.reparam f hf₀ hf₁).trans (Dipath.refl y)) := by
  set φ₁ : D(I, I) := ReflTransReparamAuxMap
  set φ₂ : D(I, I) := f.comp TransReflReparamAuxMap
  have hφ₁_le_φ₂ : ∀ (t : I), φ₁ t ≤ φ₂ t := by
    intro t
    apply Subtype.coe_le_coe.mp
    dsimp [φ₁, φ₂, ReflTransReparamAuxMap, ReflTransReparamAux, TransReflReparamAuxMap, Path.Homotopy.transReflReparamAux, DirectedMap.comp]
    show ite ((t : ℝ) ≤ 1 / 2) 0 ((2 : ℝ) * (t : ℝ) - 1) ≤ (f ⟨ite ((t : ℝ) ≤ 1 / 2) ((2 : ℝ) * (t : ℝ)) 1, _⟩ : ℝ)
    by_cases h : (t : ℝ) ≤ 2⁻¹ <;> simp [h]
    · exact (f _).2.1
    · have : (t : ℝ) ≤ 1 := t.2.2
      simp [hf₁]
      linarith
  have hφ₂₀ : φ₂ 0 = 0 := by
    show f ⟨Path.Homotopy.transReflReparamAux 0, _⟩ = 0
    nth_rewrite 3 [←hf₀]
    congr
    exact Path.Homotopy.transReflReparamAux_zero
  have hφ₂₁ : φ₂ 1 = 1 := by
    show f ⟨Path.Homotopy.transReflReparamAux 1, _⟩ = 1
    nth_rewrite 3 [←hf₁]
    congr
    exact Path.Homotopy.transReflReparamAux_one
  convert reparam p φ₁ φ₂ hφ₁_le_φ₂ (Subtype.ext reflTransReparamAux_zero)
    (Subtype.ext reflTransReparamAux_one) hφ₂₀ hφ₂₁
  · exact refl_trans_reparam_dipath p
  · rw [trans_refl_reparam_dipath (p.reparam f hf₀ hf₁)]
    ext
    rfl
/--
Given `F : Dihomotopy p q`, and `f : D(X, Y)`, there is a dihomotopy from `p.map f` to
`q.map f` given by `f ∘ F`.
-/
@[simps!]
def map {p q : Dipath x y} (F : Dihomotopy p q) (f : D(X, Y)) :
    Dihomotopy (p.map f) (q.map f) where
  toFun := f ∘ F
  map_zero_left := fun _ => by simp
  map_one_left := fun _ => by simp
  prop' := fun t s hs => by
    unfold DirectedMap.prod_const_fst DirectedMap.prod_map_mk
    cases' hs with hs hs
    case inl =>
      simp [hs]
      calc (f (F (t ,0)))
        _ = (f x) := by simp
    case inr => -- s = 1
      have : s = 1 := Set.mem_singleton_iff.mp hs
      simp [this]
      calc (f (F (t ,1)))
        _ = (f y) := by simp
  directed_toFun := (f.comp F.toDirectedMap).directed_toFun
end Dihomotopy
section
variable (p₀ p₁ : Dipath x y)
/--
Two dipaths `p₀` and `p₁` are `Dipath.PreDihomotopic` if there exists a `Dihomotopy` from `p₀` to `p₁`.
-/
def PreDihomotopic : Prop := Nonempty (Dihomotopy p₀ p₁)
/--
`Dipath.Dihomotopic` is the equivalence generated by `Dipath.PreDihomotopic`.
-/
def Dihomotopic : Prop := Relation.EqvGen PreDihomotopic p₀ p₁
end
namespace Dihomotopic
lemma equivalence : Equivalence (@Dihomotopic X _ x y) := by apply Relation.EqvGen.is_equivalence
/-- If `p` is dihomotopic with `q`, then `f ∘ p` is dihomotopic with `f ∘ q` for any directed map `f` -/
lemma map {p q : Dipath x y} (h : p.Dihomotopic q) (f : D(X, Y)) :
    Dihomotopic (p.map f) (q.map f) :=
  Relation.EqvGen.rec
    (fun _ _ h => Relation.EqvGen.rel _ _ ⟨h.some.map f⟩)
    (fun x => Relation.EqvGen.refl (x.map f))
    (fun _ _ _ h => Relation.EqvGen.symm _ _ h)
    (fun _ _ _ _ _ h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂)
  h
lemma hcomp_aid_left {p₀ p₁ : Dipath x y} (q : Dipath y z) (hp : p₀.Dihomotopic p₁) :
    (p₀.trans q).Dihomotopic (p₁.trans q) :=
  Relation.EqvGen.rec
    (fun _ _ h => Relation.EqvGen.rel _ _ ⟨h.some.hcomp (Dihomotopy.refl q)⟩)
    (fun p => Relation.EqvGen.refl (p.trans q))
    (fun _ _ _ h => Relation.EqvGen.symm _ _ h)
    (fun _ _ _ _ _ h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂)
  hp
lemma hcomp_aid_right (p : Dipath x y) {q₀ q₁ : Dipath y z} (hq : q₀.Dihomotopic q₁) :
    (p.trans q₀).Dihomotopic (p.trans q₁) :=
  Relation.EqvGen.rec
    (fun _ _ h => Relation.EqvGen.rel _ _ ⟨(Dihomotopy.refl p).hcomp h.some⟩)
    (fun q => Relation.EqvGen.refl (p.trans q))
    (fun _ _ _ h => Relation.EqvGen.symm _ _ h)
    (fun _ _ _ _ _ h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂)
  hq
/--
Suppose we have`p₀ p₁ : Dipath x y` and `q₀ q₁ : Dipath y z`.
If `p₀` is dihomotopic with `p₁` and `q₀` is dihomotopic with `q₁`,
then `p₀.trans q₀` is dihomotopic with `p₁.trans q₁`.
-/
lemma hcomp {p₀ p₁ : Dipath x y} {q₀ q₁ : Dipath y z} (hp : p₀.Dihomotopic p₁)
    (hq : q₀.Dihomotopic q₁) : (p₀.trans q₀).Dihomotopic (p₁.trans q₁) :=
  Relation.EqvGen.rec
    (fun p₀ p₁ hp₀_p₁ => by
      exact Relation.EqvGen.rec
          (fun _ _ hq₀_q₁ => Relation.EqvGen.rel _ _ ⟨hp₀_p₁.some.hcomp hq₀_q₁.some⟩)
          (fun q => Relation.EqvGen.rel _ _ ⟨hp₀_p₁.some.hcomp (Dihomotopy.refl q)⟩)
          (fun q₀ q₁ _ hp₀q₀_p₁q₁ => by
              have hp₀q₁_p₁q₂ := hcomp_aid_left q₁ (Relation.EqvGen.rel _ _ hp₀_p₁)
              have hp₁q₁_p₀q₀ := Relation.EqvGen.symm _ _ hp₀q₀_p₁q₁
              have hp₀q₀_p₁q₀ := hcomp_aid_left q₀ (Relation.EqvGen.rel _ _ hp₀_p₁)
              exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hp₀q₁_p₁q₂ hp₁q₁_p₀q₀) hp₀q₀_p₁q₀
          )
          (fun q₀ q₁ q₂ hq₀_q₁ hq₁_q₂ _ _ => by
              have hp₀q₀_p₀q₁ := hcomp_aid_right p₀ hq₀_q₁
              have hp₀q₁_p₀q₂ := hcomp_aid_right p₀ hq₁_q₂
              have hp₀q₂_p₁q₂ := hcomp_aid_left q₂ (Relation.EqvGen.rel _ _ hp₀_p₁)
              exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hp₀q₀_p₀q₁ hp₀q₁_p₀q₂) hp₀q₂_p₁q₂
          )
        hq
    )
    (fun p => by
      exact Relation.EqvGen.rec
          (fun _ _ h => hcomp_aid_right p (Relation.EqvGen.rel _ _ h))
          (fun q => Relation.EqvGen.refl (p.trans q))
          (fun _ _ _ h => Relation.EqvGen.symm _ _ h)
          (fun _ _ _ _ _ h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂)
        hq
    )
    (fun p₀ p₁ hp₀_p₁ _ => by
      have hp₁_p₀ := Relation.EqvGen.symm _ _ hp₀_p₁
      exact Relation.EqvGen.rec
          (fun q₀ q₁ hq₀_q₁ => by
            have hp₁q₀_p₀q₀ := hcomp_aid_left q₀ hp₁_p₀
            have hp₀q₀_p₀q₁ := hcomp_aid_right p₀ (Relation.EqvGen.rel _ _ hq₀_q₁)
            exact Relation.EqvGen.trans _ _ _ hp₁q₀_p₀q₀ hp₀q₀_p₀q₁
          )
          (fun q => hcomp_aid_left q hp₁_p₀)
          (fun q₀ q₁ hq₀_q₁ _ => by
            have hp₁q₁_p₁q₀ := hcomp_aid_right p₁ (Relation.EqvGen.symm _ _ hq₀_q₁)
            have hp₁q₀_p₀q₀ := hcomp_aid_left q₀ (Relation.EqvGen.symm _ _ hp₀_p₁)
            exact Relation.EqvGen.trans _ _ _ hp₁q₁_p₁q₀ hp₁q₀_p₀q₀
          )
          (fun q₀ q₁ q₂ _ _ hp₁q₀_p₀q₁ hp₁q₁_p₀q₂ => by
            have hp₀q₁_p₁q₁ := hcomp_aid_left q₁ hp₀_p₁
            exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hp₁q₀_p₀q₁ hp₀q₁_p₁q₁) hp₁q₁_p₀q₂
          )
        hq
    )
    (fun p₀ p₁ p₂ hp₀_p₁ hp₁_p₂ _ _ => by
      exact Relation.EqvGen.rec
          (fun q₀ q₁ hq₀_q₁ => by
            have hp₀q₁_p₁q₀ := hcomp_aid_left q₀ hp₀_p₁
            have hp₁q₀_p₂q₀ := hcomp_aid_left q₀ hp₁_p₂
            have hp₂q₀_p₂q₁ := hcomp_aid_right p₂ (Relation.EqvGen.rel _ _ hq₀_q₁)
            exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hp₀q₁_p₁q₀ hp₁q₀_p₂q₀) hp₂q₀_p₂q₁
          )
          (fun q => by
            have hp₀q_p₁q := hcomp_aid_left q hp₀_p₁
            have hp₁q_p₂q := hcomp_aid_left q hp₁_p₂
            exact Relation.EqvGen.trans _ _ _ hp₀q_p₁q hp₁q_p₂q
          )
          (fun q₀ q₁ hq₀_q₁ hp₀q₀_p₂q₁ => by
            have hq₁_q₀ := Relation.EqvGen.symm _ _ hq₀_q₁
            have hp₀q₁_p₀q₀ := hcomp_aid_right p₀ hq₁_q₀
            have hp₂q₁_p₂q₀ := hcomp_aid_right p₂ hq₁_q₀
            exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hp₀q₁_p₀q₀ hp₀q₀_p₂q₁) hp₂q₁_p₂q₀
          )
          (fun q₀ q₁ q₂ _ _ hp₀q₀_p₂q₁ hp₀q₁_p₂q₂ => by
            have hp₂_p₀ := Relation.EqvGen.symm _ _ (Relation.EqvGen.trans _ _ _ hp₀_p₁ hp₁_p₂)
            have hp₂q₂_p₀q₁ := hcomp_aid_left q₁ hp₂_p₀
            exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hp₀q₀_p₂q₁ hp₂q₂_p₀q₁) hp₀q₁_p₂q₂
          )
        hq
    )
  hp
/--
If `p` is a dipath, then it is dihomotopic with any monotonic subparametrization.
-/
lemma reparam (p : Dipath x y) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  p.Dihomotopic (p.reparam f hf₀ hf₁) := by
  set p' := p.reparam f hf₀ hf₁
  set p₁ := ((refl x).trans p)
  set p₂ := (p'.trans (refl y))
  have h₁ : p₁.PreDihomotopic p := ⟨Dihomotopy.refl_trans p⟩
  have h₂ : p₁.PreDihomotopic p₂ := ⟨Dihomotopy.refl_trans_to_reparam_trans_refl p f hf₀ hf₁⟩
  have h₃ : p'.PreDihomotopic p₂ := ⟨Dihomotopy.trans_refl p'⟩
  have h₁ : p.Dihomotopic p₁ := Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h₁)
  have h₂ : p₁.Dihomotopic p₂ := Relation.EqvGen.rel _ _ h₂
  have h₃ : p₂.Dihomotopic p' := Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h₃)
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ h₁ h₂) h₃
/--
The setoid on `Dipath`s defined by the equivalence relation `Dipath.Dihomotopic`. That is, two paths are
equivalent if there is a chain of `Dihomotopies` starting in one and ending in the other.
-/
protected def setoid (x y : X) : Setoid (Dipath x y) := ⟨Dihomotopic, equivalence⟩
/--
The quotient on `Dipath x y` by the equivalence relation `Dipath.Dihomotopic`.
-/
protected def Quotient (x y : X) := Quotient (Dihomotopic.setoid x y)
attribute [local instance] Dihomotopic.setoid
instance : Inhabited (Dihomotopic.Quotient x x) :=
  ⟨Quotient.mk' <| Dipath.refl x⟩
/- The composition of dipath dihomotopy classes. This is `Dipath.trans` descended to the quotient. -/
def Quotient.comp (P₀ : Dipath.Dihomotopic.Quotient x y) (P₁ : Dipath.Dihomotopic.Quotient y z) :
  Dipath.Dihomotopic.Quotient x z :=
Quotient.map₂ Dipath.trans (fun (_ : Dipath x y) _ hp (_ : Dipath y z) _ hq => (hcomp hp hq)) P₀ P₁
lemma comp_lift (P₀ : Dipath x y) (P₁ : Dipath y z) : ⟦P₀.trans P₁⟧ = Quotient.comp ⟦P₀⟧ ⟦P₁⟧ := rfl
/- The image of a dipath dihomotopy class `P₀` under a directed map `f`.
    This is `Dipath.map` descended to the quotient -/
def Quotient.mapFn (P₀ : Dipath.Dihomotopic.Quotient x y) (f : D(X, Y)) :
  Dipath.Dihomotopic.Quotient (f x) (f y) :=
Quotient.map (fun (q : Dipath x y) => q.map f) (fun _ _ h => Dipath.Dihomotopic.map h f) P₀
lemma map_lift (P₀ : Dipath x y) (f : D(X, Y)) :
  ⟦P₀.map f⟧ = Quotient.mapFn ⟦P₀⟧ f := rfl
lemma quot_reparam (γ : Dipath x y) {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    @Eq (Dipath.Dihomotopic.Quotient _ _) ⟦γ.reparam f hf₀ hf₁⟧ ⟦γ⟧ := by
  symm
  exact Quotient.eq.mpr (Dipath.Dihomotopic.reparam γ f hf₀ hf₁)
lemma hpath_hext {x₀ x₁ x₂ x₃ : X} {p₁ : Dipath x₀ x₁} {p₂ : Dipath x₂ x₃} (hp : ∀ t, p₁ t = p₂ t) :
    @HEq (Dipath.Dihomotopic.Quotient _ _) ⟦p₁⟧ (Dipath.Dihomotopic.Quotient _ _) ⟦p₂⟧ := by
  obtain rfl : x₀ = x₂ := by convert hp 0 <;> simp
  obtain rfl : x₁ = x₃ := by convert hp 1 <;> simp
  have hp' : p₁ = p₂ := by
    apply Dipath.ext
    funext t
    exact hp t
  subst p₂
  rfl
end Dihomotopic
end Dipath
end
end Lean4_directed_path_homotopy
/-! Source module: Lean4.fundamental_category -/
section Lean4_fundamental_category
/-
  This file contains the definition of the fundamental category of a directed space.
  We follow the structure of the undirected version found at:
  https://leanprover-community.github.io/mathlib_docs/algebraic_topology/fundamental_groupoid/basic.html#fundamental_groupoid
-/
open DirectedMap
open CategoryTheory
universe u v
variable {X : Type u} {Y : Type v} [DirectedSpace X] [DirectedSpace Y] {x₀ x₁ : X}
open scoped unitInterval
noncomputable section
namespace Dipath
namespace Dihomotopy
open Path.Homotopy
section assoc
lemma transAssocReparamAux_directed : DirectedMap.Directed
  ({ toFun := fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩} : C(I, I)) := by
  apply DirectedUnitInterval.directed_of_monotone _
  intros x y hxy
  unfold transAssocReparamAux
  simp
  have : (x : ℝ) ≤ (y : ℝ) := hxy
  split_ifs with h₀ h₁ h₂ h₃ h₄ h₅
  · linarith
  · linarith
  · push_neg at h₂
    have : 0 ≤ (y : ℝ) := le_trans (by norm_num) (le_of_lt h₂)
    have : 1 ≤ (y : ℝ) + 1 := by linarith
    calc 2 * (x : ℝ)
      _ ≤ 2 * 4⁻¹ := (mul_le_mul_iff_of_pos_left (by norm_num)).mpr h₀
      _ = (2⁻¹ : ℝ) * 1 := by norm_num
      _ ≤ (2⁻¹ : ℝ) * (↑y + 1) := (mul_le_mul_iff_of_pos_left (by norm_num)).mpr this
  · linarith
  · linarith
  · push_neg at h₅
    calc (x : ℝ) + (4⁻¹ : ℝ)
      _ = 4⁻¹ + ↑x := by ring
      _ ≤ 4⁻¹ + 2⁻¹ := add_le_add_right h₃ 4⁻¹
      _ = 2⁻¹ + 4⁻¹ := by ring
      _ = 2⁻¹ * (2⁻¹ + 1) := by norm_num
      _ ≤ 2⁻¹ * (↑y + 1) := (mul_le_mul_iff_of_pos_left (by norm_num)).mpr (by linarith)
  · linarith
  · linarith
  · apply (mul_le_mul_iff_of_pos_left (show 0 < (2⁻¹ : ℝ) by norm_num)).mpr
    linarith [Subtype.coe_le_coe.mpr hxy]
def transAssocReparamAuxMap : D(I, I) where
  toFun := fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩
  directed_toFun := transAssocReparamAux_directed
lemma trans_assoc_reparam_directed {x₀ x₁ x₂ x₃ : X} (p : Dipath x₀ x₁) (q : Dipath x₁ x₂) (r : Dipath x₂ x₃) :
    (p.trans q).trans r = (p.trans (q.trans r)).reparam
      transAssocReparamAuxMap
      (Subtype.ext transAssocReparamAux_zero)
      (Subtype.ext transAssocReparamAux_one) := by
  ext t
  have : (p.trans q).trans r t =  (p.toPath.trans q.toPath).trans r.toPath t := rfl
  rw [this, trans_assoc_reparam p.toPath q.toPath r.toPath]
  rfl
/--
For any three dipaths `p q r`, `(p.trans q).trans r` is dihomotopic with `p.trans (q.trans r)`.
-/
def trans_assoc {x₀ x₁ x₂ x₃ : X} (p : Dipath x₀ x₁) (q : Dipath x₁ x₂) (r : Dipath x₂ x₃) :
    ((p.trans q).trans r).Dihomotopic (p.trans (q.trans r)) := by
  have := Dihomotopic.reparam (p.trans (q.trans r)) transAssocReparamAuxMap
    (Subtype.ext transAssocReparamAux_zero)
    (Subtype.ext transAssocReparamAux_one)
  rw [←trans_assoc_reparam_directed] at this
  exact Relation.EqvGen.symm _ _ this
end assoc
end Dihomotopy
end Dipath
/-
 Definition of the fundamental category and of the functor sending a directed space to its
 fundamental category
-/
@[ext]
structure FundamentalCategory (X : Type u) where
  as : X
namespace FundamentalCategory
@[simps]
def equiv (X : Type*) : FundamentalCategory X ≃ X where
  toFun x := x.as
  invFun x := .mk x
  left_inv _ := rfl
  right_inv _ := rfl
@[simp]
lemma isEmpty_iff (X : Type*) :
    IsEmpty (FundamentalCategory X) ↔ IsEmpty X :=
  equiv _ |>.isEmpty_congr
instance (X : Type*) [IsEmpty X] :
    IsEmpty (FundamentalCategory X) :=
  equiv _ |>.isEmpty
@[simp]
lemma nonempty_iff (X : Type*) :
    Nonempty (FundamentalCategory X) ↔ Nonempty X :=
  equiv _ |>.nonempty_congr
instance (X : Type*) [Nonempty X] :
    Nonempty (FundamentalCategory X) :=
  equiv _ |>.nonempty
@[simp]
lemma subsingleton_iff (X : Type*) :
    Subsingleton (FundamentalCategory X) ↔ Subsingleton X :=
  equiv _ |>.subsingleton_congr
instance (X : Type*) [Subsingleton X] :
    Subsingleton (FundamentalCategory X) :=
  equiv _ |>.subsingleton
instance {X : Type u} [Inhabited X] : Inhabited (FundamentalCategory X) :=
  ⟨⟨default⟩⟩
attribute [local instance] Dipath.Dihomotopic.setoid
instance : CategoryTheory.Category (FundamentalCategory X) where
  Hom x y := Dipath.Dihomotopic.Quotient x.as y.as
  id x := ⟦Dipath.refl x.as⟧
  comp {_ _ _} := Dipath.Dihomotopic.Quotient.comp
  id_comp {x _} f :=
    Quotient.inductionOn f fun a =>
      show ⟦(Dipath.refl x.as).trans a⟧ = ⟦a⟧ from Quotient.sound (Relation.EqvGen.rel _ _ ⟨Dipath.Dihomotopy.refl_trans a⟩)
  comp_id {_ y} f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.trans (Dipath.refl y.as)⟧ = ⟦a⟧ from Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨Dipath.Dihomotopy.trans_refl a⟩))
  assoc {_ _ _ _} f g h :=
    Quotient.inductionOn₃ f g h fun p q r =>
      show ⟦(p.trans q).trans r⟧ = ⟦p.trans (q.trans r)⟧ from
        Quotient.sound (Dipath.Dihomotopy.trans_assoc p q r)
lemma comp_eq (x y z : FundamentalCategory X) (p : x ⟶ y) (q : y ⟶ z) :
    p ≫ q = p.comp q := rfl
lemma id_eq_path_refl (x : FundamentalCategory X) :
    𝟙 x = ⟦Dipath.refl x.as⟧ := rfl
@[reducible]
def fundamentalCategoryFunctor : dTopCat ⥤ CategoryTheory.Cat where
      obj X := { α := FundamentalCategory X }
      map f := { toFunctor := {
      obj := fun x => ⟨f x.as⟩
      map := fun {X Y} p => by exact p.mapFn f
      map_id := fun X => by
        change Dipath.Dihomotopic.Quotient.mapFn
          ⟦Dipath.refl X.as⟧ f = ⟦Dipath.refl (f X.as)⟧
        rw [← Dipath.Dihomotopic.map_lift]
        congr 1
      map_comp := fun {x y z} p q => by
        refine Quotient.inductionOn₂ p q fun a b => ?_
        change Dipath.Dihomotopic.Quotient.mapFn
          (Dipath.Dihomotopic.Quotient.comp ⟦a⟧ ⟦b⟧) f =
          Dipath.Dihomotopic.Quotient.comp ⟦a.map f⟧ ⟦b.map f⟧
        rw [←Dipath.Dihomotopic.comp_lift a b,
          ←Dipath.Dihomotopic.map_lift (a.trans b) f,
          Dipath.map_trans,
          ←Dipath.Dihomotopic.comp_lift]
    }}
      map_id X := by
        apply CategoryTheory.Cat.ext
        simp only
        change _ = 𝟭 (FundamentalCategory X)
        congr
        ext x y p
        refine' Quotient.inductionOn p fun q => _
        rw [← Dipath.Dihomotopic.map_lift]
        conv_rhs => rw [←q.map_id]
        rfl
      map_comp f g := by
        apply CategoryTheory.Cat.ext
        simp only
        congr
        ext x y p
        refine' Quotient.inductionOn p fun q => _
        simp only [Quotient.map_mk, Dipath.map_map, Quotient.eq']
        rfl
scoped notation "dπ" => FundamentalCategory.fundamentalCategoryFunctor
scoped notation "dπₓ" => FundamentalCategory.fundamentalCategoryFunctor.obj
scoped notation "dπₘ" => FundamentalCategory.fundamentalCategoryFunctor.map
lemma map_eq {X Y : dTopCat} {x₀ x₁ : X} (f : D(X, Y)) (p : Dipath.Dihomotopic.Quotient x₀ x₁) :
  (dπₘ f).toFunctor.map p = p.mapFn f := rfl
/-- Help the typechecker by converting a point in the fundamental category back to a point in
the underlying directed space. -/
@[reducible]
def toTop {X : dTopCat} (x : dπₓ X) : X := x.as
/-- Help the typechecker by converting a point in a directed space to a
point in the fundamental category of that space -/
@[reducible]
def fromTop {X : dTopCat} (x : X) : dπₓ X := ⟨x⟩
/-- Help the typechecker by converting an arrow in the fundamental category of
a directed space back to a directed path in that space (i.e., `Dipath.Dihomotopic.Quotient`). -/
@[reducible]
def toPath {X : dTopCat} {x₀ x₁ : dπₓ X} (p : x₀ ⟶ x₁) :
  Dipath.Dihomotopic.Quotient (X := X) x₀.as x₁.as := p
/-- Help the typechecker by convering a directed path in a directed space to an arrow in the
fundamental category of that space. -/
@[reducible]
def fromPath {X : dTopCat} {x₀ x₁ : X} (p : Dipath.Dihomotopic.Quotient x₀ x₁) :
  FundamentalCategory.mk x₀ ⟶ FundamentalCategory.mk x₁ := p
end FundamentalCategory
end
end Lean4_fundamental_category
/-! Source module: Lean4.dipath_subtype -/
section Lean4_dipath_subtype
/-
  This file contains properties of dipaths contained in directed subspaces of a directed space.
  In particular, properties about their equivalence classes in the fundamental category.
-/
open Set
open scoped FundamentalCategory unitInterval
attribute [local instance] Dipath.Dihomotopic.setoid
namespace DiSubtype
variable {X : dTopCat} {X₀ : Set X}
lemma subtypeHom_eq_coe (x : X₀) : (dTopCat.DirectedSubtypeHom X₀) x = (x : X) := rfl
lemma range_dipath_map_inclusion {x y : X₀} (γ : Dipath x y) : range (γ.map (DirectedSubtypeInclusion X₀)) ⊆ X₀ := by
  rintro z ⟨t, ht⟩
  rw [←ht]
  show (dTopCat.DirectedSubtypeHom X₀) (γ t) ∈ X₀
  rw [subtypeHom_eq_coe]
  exact Subtype.mem (γ t)
lemma subtype_path_class_eq_map {x y : X₀} (γ : Dipath x y) :
    (dπₘ (dTopCat.DirectedSubtypeHom X₀)).toFunctor.map ⟦γ⟧ = ⟦(γ.map (DirectedSubtypeInclusion X₀))⟧ :=
  rfl
variable {x y z : X}
lemma source_elt_of_image_subset {γ : Dipath x y} (hγ : range γ ⊆ X₀) : x ∈ X₀ := γ.source ▸ (hγ (mem_range_self 0))
lemma target_elt_of_image_subset {γ : Dipath x y} (hγ : range γ ⊆ X₀) : y ∈ X₀ := γ.target ▸ (hγ (mem_range_self 1))
def SubtypePath {γ : Dipath x y} (hγ : range γ ⊆ X₀) :
    Path (⟨x, source_elt_of_image_subset hγ⟩ : X₀) ⟨y, target_elt_of_image_subset hγ⟩ where
  toFun := fun t => ⟨γ t, hγ (mem_range_self t)⟩
  continuous_toFun := Continuous.subtype_mk γ.continuous (fun t => hγ (mem_range_self t))
  source' := by simp
  target' := by simp
def SubtypeDipath (γ : Dipath x y) (hγ : range γ ⊆ X₀) :
    Dipath (⟨x, source_elt_of_image_subset hγ⟩ : X₀) ⟨y, target_elt_of_image_subset hγ⟩ where
  toPath := SubtypePath hγ
  dipath_toPath := γ.dipath_toPath
lemma map_subtypeDipath_eq {x y : X} (γ : Dipath x y) (hγ : range γ ⊆ X₀) :
    (dπₘ (dTopCat.DirectedSubtypeHom X₀)).toFunctor.map ⟦SubtypeDipath γ hγ⟧ = ⟦γ⟧ := by
  rw [subtype_path_class_eq_map]
  congr 1
lemma subtypeDipath_of_included_dipath_eq {x y : X₀} (γ : Dipath x y) :
    SubtypeDipath (γ.map (DirectedSubtypeInclusion X₀)) (range_dipath_map_inclusion γ) =
    γ.cast (by ext; rw [←subtypeHom_eq_coe x]; rfl) (by ext; rw [←subtypeHom_eq_coe y]; rfl) := by
  ext t
  rfl
lemma range_refl_subset_of_mem {x : X} (hx : x ∈ X₀) : range (Dipath.refl x) ⊆ X₀ := by
  rw [Dipath.refl_range]
  exact singleton_subset_iff.mpr hx
lemma subtype_refl {x : X} (hx : x ∈ X₀) : (SubtypeDipath (Dipath.refl x) (range_refl_subset_of_mem hx)) = Dipath.refl (⟨x, hx⟩ : X₀) := rfl
lemma subsets_of_trans_subset {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₀) :
    range γ₁ ⊆ X₀ ∧ range γ₂ ⊆ X₀ := by
  rw [Dipath.trans_range] at hγ
  exact ⟨subset_trans subset_union_left hγ, subset_trans subset_union_right hγ⟩
lemma trans_subset_of_subsets  {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ₁ : range γ₁ ⊆ X₀) (hγ₂ : range γ₂ ⊆ X₀) :
    range (γ₁.trans γ₂) ⊆ X₀ := by
  rw [Dipath.trans_range]
  exact union_subset hγ₁ hγ₂
lemma subtype_trans {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₀) :
    (SubtypeDipath γ₁ (subsets_of_trans_subset hγ).1).trans (SubtypeDipath γ₂ (subsets_of_trans_subset hγ).2) =
    SubtypeDipath (γ₁.trans γ₂) hγ := by
  ext t
  show _ = (γ₁.trans γ₂) t
  rw [Dipath.trans_apply, Dipath.trans_apply,]
  split_ifs <;> rfl
lemma subtype_reparam {γ : Dipath x y} (hγ : range γ ⊆ X₀) {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1):
    SubtypeDipath (γ.reparam f hf₀ hf₁) ((Dipath.range_reparam γ f hf₀ hf₁).symm ▸ hγ) =
    (SubtypeDipath γ hγ).reparam f hf₀ hf₁ :=
  rfl
lemma reparam_subset_of_subset {γ : Dipath x y} (hγ : range γ ⊆ X₀) {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    range (γ.reparam f hf₀ hf₁) ⊆ X₀ := by
  rw [Dipath.range_reparam]
  exact hγ
def DihomotopyOfSubtype {γ γ' : Dipath x y} (hγ : range γ ⊆ X₀) (hγ' : range γ' ⊆ X₀)
  {F : Dipath.Dihomotopy γ γ'} (hF : range F ⊆ X₀) :
    Dipath.Dihomotopy (SubtypeDipath γ hγ) (SubtypeDipath γ' hγ') where
  toFun := fun t => ⟨F t, hF (mem_range_self t)⟩
  directed_toFun := fun a b p hp => F.directed_toFun _ hp
  map_zero_left := fun t => by simp; rfl
  map_one_left := fun t => by simp; rfl
  prop' := fun t p hp => by
    have := F.prop' t p hp
    ext
    show _ = (γ.toDirectedMap) p
    rw [←this]
    rfl
lemma dihomSubtype_of_dihom_range_subset {γ γ' : Dipath x y} (hγ : range γ ⊆ X₀) (hγ' : range γ' ⊆ X₀)
  {F : Dipath.Dihomotopy γ γ'} (hF : range F ⊆ X₀) :
    @Eq (Dipath.Dihomotopic.Quotient _ _) ⟦SubtypeDipath γ hγ⟧ ⟦SubtypeDipath γ' hγ'⟧ :=
Quotient.eq.mpr (Relation.EqvGen.rel _ _ ⟨DihomotopyOfSubtype hγ hγ' hF⟩)
end DiSubtype
end Lean4_dipath_subtype
/-! Source module: Lean4.fraction_equalities -/
section Lean4_fraction_equalities
namespace FractionEqualities
lemma one_sub_inverse_of_add_one {n : ℝ} (hn : n + 1 ≠ 0) :
    1 - 1 / (n + 1) = n / (n + 1) := by
  field_simp [hn]
  ring
lemma frac_cancel {a b c : ℝ} (hb : b ≠ 0) : (a / b) * (b / c) = a / c := by
  by_cases hc : c = 0
  · simp [hc]
  · field_simp [hb, hc]
lemma frac_cancel' {a b c : ℝ} (hb : b ≠ 0) : (b / a) * (c / b) = c / a := by
  rw [mul_comm]
  exact frac_cancel hb
lemma one_sub_frac {a b : ℝ} (hb : b + 1 ≠ 0) : (1 - (a + 1)/(b+1)) = (b - a) / (b + 1) := by
  field_simp [hb]
  ring
lemma frac_special {a b c : ℝ} (hbc : b ≠ c) (hc : c + 1 ≠ 0) :
    (a + (b + 1)) / (c + 1) = (1 - (b + 1) / (c + 1)) * (a / (c - b)) + (b + 1) / (c + 1) := by
  rw [one_sub_frac hc, frac_cancel']
  · exact (div_add_div_same _ _ _).symm
  · exact sub_ne_zero_of_ne hbc.symm
/--
  For any `i n : ℕ` with `i > 0` and `i ≤ (n + 1) * i`, we have that `1 / (n + 1) = i / ((n + 1) * i)`.
-/
lemma cancel_common_factor {i n : ℕ} (i_pos : 0 < i) (hi_n : (i - 1).succ ≤ ((n+1) * i - 1).succ) :
    Fraction.ofPos (Nat.succ_pos n) = Fraction (Nat.succ_pos _) hi_n := by
  apply Subtype.ext
  simp only [Fraction.ofPos_coe, Fraction.Fraction_coe]
  have hi : (i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt i_pos)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hi_succ : (i - 1).succ = i := Nat.succ_pred_eq_of_pos i_pos
  have hn_succ : ((n + 1) * i - 1).succ = (n + 1) * i :=
    Nat.succ_pred_eq_of_pos (mul_pos (Nat.succ_pos n) i_pos)
  simp only [hi_succ, hn_succ, Nat.cast_succ, Nat.cast_mul]
  field_simp [hi, ne_of_gt hn]
  ring
end FractionEqualities
end Lean4_fraction_equalities
/-! Source module: Lean4.SplitPath.split_properties -/
section Lean4_SplitPath_split_properties
/-
  This file contains many lemmas about relations that the parts of a split path satisfy.
-/
open scoped unitInterval
open SplitDipath Set
noncomputable section
universe u
variable {X : Type u} [DirectedSpace X] {x₀ x₁ : X}
namespace SplitProperties
--TODO: Rework some of these statement to make them more general: that should make proving the
-- specfic versions easier.
/-! ### General -/
lemma firstPart_cast {x₀' x₁' : X} (γ : Dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) (T : I) :
  (FirstPart (γ.cast hx₀ hx₁) T) = (FirstPart γ T).cast hx₀ rfl := rfl
lemma secondPart_cast {x₀' x₁' : X} (γ : Dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) (T : I) :
  (SecondPart (γ.cast hx₀ hx₁) T) = (SecondPart γ T).cast rfl hx₁ := rfl
lemma firstPart_eq_of_split_point_eq (γ : Dipath x₀ x₁) {T T' : I} (hT : T = T') :
  (FirstPart γ T) = (FirstPart γ T').cast rfl (congr_arg γ hT) := by subst_vars; rfl
lemma secondPart_eq_of_split_point_eq (γ : Dipath x₀ x₁) {T T' : I} (hT : T = T') :
  (SecondPart γ T) = (SecondPart γ T').cast (congr_arg γ hT) rfl := by subst_vars; rfl
lemma firstPart_eq_of_point_eq (γ : Dipath x₀ x₁) {T T': I} (h : T = T') (t : I) :
  (FirstPart γ T) t = (FirstPart γ T') t := by subst_vars; rfl
lemma secondPart_eq_of_point_eq (γ : Dipath x₀ x₁) {T T': I} (h : T = T') (t : I) :
  (SecondPart γ T) t = (SecondPart γ T') t := by subst_vars; rfl
lemma interval_cast {γ : Dipath x₀ x₁} {A : Set X} {a b a' b' : I} (h_im : A = γ '' Icc a b)
      (ha : a' = a) (hb : b' = b) :
    A = γ '' Icc a' b' := by subst_vars; rfl
/-! ### First Part -/
lemma firstPart_image (γ : Dipath x₀ x₁) (T a b : I) (h_ab : a ≤ b):
    (FirstPart γ T) '' Icc a b = γ '' Icc (T * a) (T * b) := by
  ext z
  constructor
  · rintro ⟨t, t_a_b, ht⟩
    rw [first_part_apply] at ht
    use T * t
    constructor
    constructor
    · exact Subtype.coe_le_coe.mp $ mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr t_a_b.1) T.2.1
    · exact Subtype.coe_le_coe.mp $ mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr t_a_b.2) T.2.1
    · exact ht
  · rintro ⟨t, t_Ta_Tb, ht⟩
    by_cases h : T = 0
    · use a
      constructor
      · simp; exact h_ab
      · show γ (T * a) = z
        simp [h] at t_Ta_Tb
        rw [h, zero_mul]
        exact t_Ta_Tb ▸ ht
    have hT : 0 < T := lt_of_le_of_ne unitInterval.nonneg' (show T ≠ 0 by exact h).symm
    have h₁ : (a : ℝ) ≤ (t / T : ℝ) :=
      (le_div_iff₀ $ Subtype.coe_lt_coe.mpr hT).mpr $ mul_comm (a : ℝ) T ▸ Subtype.coe_le_coe.mpr t_Ta_Tb.1
    have h₂ : (t / T : ℝ) ≤ b :=
      (div_le_iff₀ $ Subtype.coe_lt_coe.mpr hT).mpr $ mul_comm (b : ℝ) T ▸ Subtype.coe_le_coe.mpr t_Ta_Tb.2
    use ⟨t / T, le_trans a.2.1 h₁, le_trans h₂ b.2.2⟩
    constructor
    · exact ⟨h₁, h₂⟩
    · rw [first_part_apply]
      convert ht using 2
      simp
      apply Subtype.coe_inj.mp
      show (T : ℝ) * (t / T) = t
      rw [mul_div_left_comm, div_self]
      · exact mul_one (t : ℝ)
      · exact unitInterval.coe_ne_zero.mpr h
lemma firstPart_range (γ : Dipath x₀ x₁) (T : I) :
    range (FirstPart γ T) = (γ '' Icc 0 T) := by
  rw [Dipath.range_eq_image_I _]
  convert firstPart_image γ T 0 1 zero_le_one <;> norm_num
lemma firstPart_range_interval (γ : Dipath x₀ x₁) {n : ℕ} (h : 0 < n) :
    range (FirstPart γ (Fraction.ofPos h)) = γ ''  Icc 0 (Fraction.ofPos h) :=
  firstPart_range γ (Fraction.ofPos h)
lemma firstPart_range_interval_coe (γ : Dipath x₀ x₁) {n : ℕ} (h : 0 < n):
    range (FirstPart γ (Fraction.ofPos h)) = γ.extend ''  Icc 0 (1/(↑n)) := by
  rw [firstPart_range_interval γ h, ←Dipath.image_extend_eq_image, Fraction.ofPos_coe]
  rfl
/--
If `γ` is a path, then the image of `[i/(d+1), (i+1)/(d+1)]` under `γ` split at `(d+1)/(n+1)` is the
image of `[i/(n+1), (i+1)/(n+1)]` under `γ`
-/
lemma firstPart_range_interval_partial (γ : Dipath x₀ x₁) {n d i : ℕ} (hd : d.succ < n.succ) (hi : i < d.succ) :
  (FirstPart γ (Fraction (Nat.succ_pos n) (le_of_lt hd))) '' Icc -- First part at (d + 1)/(n + 1)
    (Fraction (Nat.succ_pos d) (le_of_lt hi)) -- frac i/(d+1)
    (Fraction (Nat.succ_pos d) (Nat.succ_le_of_lt hi)) -- frac (i+1)/(d+1)
    = γ ''  Icc
    (Fraction (Nat.succ_pos n) (le_of_lt (lt_trans hi hd))) -- frac i/(n+1)
    (Fraction (Nat.succ_pos n) (Nat.succ_le_of_lt (lt_trans hi hd))) -- frac (i+1)/(n+1)
  := by
  convert firstPart_image γ (Fraction (Nat.succ_pos n) (le_of_lt hd))
    (Fraction (Nat.succ_pos d) (le_of_lt hi)) (Fraction (Nat.succ_pos d) (Nat.succ_le_of_lt hi))
    (show _ ≤ _ by exact (Fraction.lt_frac_succ hi).le) <;>
  simp [Fraction] <;>
  apply Subtype.coe_inj.mp <;>
  simp <;>
  refine (FractionEqualities.frac_cancel' ?_).symm <;>
  rw [←Nat.cast_succ] <;>
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
/--
If `γ` is a path, then the image of `[i/(d+1), (i+1)/(d+1)]` under `γ` split at `(d+1)/(n+1)` is the
image of `[i/(n+1), (i+1)/(n+1)]` under `γ`.
-/
lemma firstPart_range_interval_partial_coe (γ : Dipath x₀ x₁) {n d i : ℕ} (hd : d.succ < n.succ) (hi : i < d.succ) :
    (FirstPart γ (Fraction (Nat.succ_pos n) (le_of_lt hd))).extend '' Icc (↑i/(↑d+1)) ((↑i+1)/(↑d+1))
      = γ.extend ''  Icc (↑i/(↑n+1)) ((↑i+1)/(↑n+1)) := by
  have := firstPart_range_interval_partial γ hd hi
  rw [←Dipath.image_extend_eq_image] at this
  rw [←Dipath.image_extend_eq_image] at this
  convert this <;> exact (Nat.cast_succ _).symm
/-! ### Second Part -/
lemma secondPart_image (γ : Dipath x₀ x₁) (T a b : I) (h_ab : a ≤ b):
    (SecondPart γ T) '' Icc a b = γ '' Icc
      ⟨σ T * a + T, interp_left_mem_I T a⟩
      ⟨σ T * b + T, interp_left_mem_I T b⟩ := by
  ext z
  constructor
  · rintro ⟨t, t_a_b, ht⟩
    rw [second_part_apply] at ht
    use ⟨σ T * t + T, interp_left_mem_I T t⟩
    exact ⟨⟨unitIAux.interp_left_le_of_le T t_a_b.1, unitIAux.interp_left_le_of_le T t_a_b.2⟩, ht⟩
  · rintro ⟨t, t_Ta_Tb, ht⟩
    by_cases h : T = 1
    · use a
      constructor
      · simp; exact h_ab
      · show γ (_) = z
        simp [h] at t_Ta_Tb
        simp [t_Ta_Tb] at ht
        simp [h, ht]
    have hT : T < 1 := lt_of_le_of_ne unitInterval.le_one' (show T ≠ 1 by exact h)
    have : (T : ℝ) < 1 := Subtype.coe_lt_coe.mpr hT
    have : (σ T : ℝ) > 0 := show (1 - T : ℝ) > 0 by linarith
    have h₁ : (a : ℝ) ≤ ((t - T) / (σ T) : ℝ) := by
      apply (le_div_iff₀ this).mpr
      rw [mul_comm]
      have : (σ T : ℝ) * a  + T ≤ t := t_Ta_Tb.1
      linarith
    have h₂ : ((t - T) / (1 - T) : ℝ) ≤ b := by
      apply (div_le_iff₀ this).mpr
      rw [mul_comm]
      have : (t : ℝ) ≤ (σ T : ℝ) * b + T := t_Ta_Tb.2
      linarith
    use ⟨(t - T) / (1 - T), le_trans a.2.1 h₁, le_trans h₂ b.2.2⟩
    constructor
    · exact ⟨h₁, h₂⟩
    · rw [second_part_apply]
      convert ht using 2
      simp
      apply Subtype.coe_inj.mp
      show (σ T : ℝ) * ((t-T)/(σ T)) + T = t
      rw [mul_div_left_comm, div_self]
      ring
      exact ne_of_gt this
lemma secondPart_range (γ : Dipath x₀ x₁) (T : I) :
    range (SecondPart γ T) = γ '' Icc T 1  := by
  rw [Dipath.range_eq_image_I _]
  convert secondPart_image γ T 0 1 zero_le_one using 3 <;> simp
/--
  When γ is a dipath, an we split it on the intervals [0, 1/(n+1)] and [1/(n+1), 1], then the image of γ of
  [(i+1)/(n+1), (i+2)/(n+1)] is equal to the image the second part of γ of [i/n, (i+1)/n]
-/
lemma secondPart_range_interval (γ : Dipath x₀ x₁) {i n : ℕ} (hi : i < n) (hn : 0 < n):
    (SecondPart γ (Fraction.ofPos (Nat.succ_pos n))) '' Icc
      (Fraction hn (le_of_lt hi)) (Fraction hn (Nat.succ_le_of_lt hi)) =
    γ ''  Icc (Fraction (Nat.succ_pos n) (show i+1 ≤ n+1 by exact (le_of_lt (Nat.succ_lt_succ hi))))
              (Fraction (Nat.succ_pos n) (show i+2 ≤ n+1 by exact Nat.succ_lt_succ (Nat.succ_le_of_lt hi))) := by
  apply interval_cast (secondPart_image γ (Fraction.ofPos (Nat.succ_pos n)) _ _
    (le_of_lt (Fraction.lt_frac_succ hi)))
  · apply Subtype.ext
    simp only [Fraction.Fraction_coe, unitInterval.coe_symm_eq, Nat.cast_succ,
      Nat.cast_zero, Nat.cast_one]
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
    have hn1 : (n : ℝ) + 1 ≠ 0 := ne_of_gt (add_pos (Nat.cast_pos.mpr hn) one_pos)
    field_simp [hn0, hn1]
    ring
  · apply Subtype.ext
    simp only [Fraction.Fraction_coe, unitInterval.coe_symm_eq, Nat.cast_succ,
      Nat.cast_zero, Nat.cast_one]
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
    have hn1 : (n : ℝ) + 1 ≠ 0 := ne_of_gt (add_pos (Nat.cast_pos.mpr hn) one_pos)
    field_simp [hn0, hn1]
    ring
/--
  When γ is a dipath, an we split it on the intervals [0, 1/(n+1)] and [1/(n+1), 1], then the image of γ of
  [(i+1)/(n+1), (i+2)/(n+1)] is equal to the image the second part of γ of [i/n, (i+1)/n].
  Version with interval of real numbers
-/
lemma secondPart_range_interval_coe (γ : Dipath x₀ x₁) {i n : ℕ} (hi : i < n) (hn : 0 < n):
    (SecondPart γ (Fraction.ofPos (Nat.succ_pos n))).extend '' Icc (↑i/↑n) ((↑i+1)/↑n) =
    γ.extend ''  Icc ((↑i+1)/(↑n+1)) ((↑i+1+1)/(↑n+1)) := by
  have := secondPart_range_interval γ hi hn
  rw [←Dipath.image_extend_eq_image] at this
  rw [←Dipath.image_extend_eq_image] at this
  convert this
  exact (Nat.cast_succ i).symm
  exact (Nat.cast_succ i).symm
  exact (Nat.cast_succ n).symm
  rw [←Nat.cast_succ i]
  rw [←Nat.cast_succ i.succ]
  exact (Nat.cast_succ n).symm
/--
  When γ is a dipath, an we split it on the intervals [0, (d+1)/(n+1)] and [(d+1)/(n+1), 1], then the image of γ of
  [(i+d.succ)/(n+1), (i+d.succ+1)/(n+1)] is equal to the image the second part of γ of [(i/(n-d), (i+1)/(n-d)].
-/
lemma secondPart_range_partial_interval (γ : Dipath x₀ x₁) {i d n : ℕ} (hd : d.succ < n.succ) (hi : i < n - d) :
    (SecondPart γ (Fraction (Nat.succ_pos n) (le_of_lt hd))) '' Icc
      (Fraction (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hd)) (le_of_lt hi)) -- i/(n-d)
      (Fraction (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hd)) (Nat.succ_le_of_lt hi)) -- (i+1)/(n-d)
      =
    γ ''  Icc
      (Fraction (Nat.succ_pos n) (show i+d.succ ≤ n.succ by
        apply le_of_lt
        have : i < n.succ - d.succ := (Nat.succ_sub_succ n d).symm ▸ hi
        exact lt_tsub_iff_right.mp this
      )) -- (i+d+1)/(n+1)
      (Fraction (Nat.succ_pos n) (show i+d.succ + 1 ≤ n.succ by
        apply Nat.succ_le_of_lt
        have : i < n.succ - d.succ := (Nat.succ_sub_succ n d).symm ▸ hi
        exact lt_tsub_iff_right.mp this
      )) -- (i+d+2)/(n+1)
    := by
  apply interval_cast (secondPart_image γ (Fraction (Nat.succ_pos n) (le_of_lt hd)) _ _
    (le_of_lt (Fraction.lt_frac_succ hi)))
  · apply Subtype.ext
    simp only [Fraction.Fraction_coe, Fraction.ofPos_coe, unitInterval.coe_symm_eq,
      Nat.cast_add, Nat.cast_succ]
    have : d < n := Nat.lt_of_succ_lt_succ hd
    rw [Nat.cast_sub (le_of_lt this)]
    have hdlt : (↑d : ℝ) < ↑n := Nat.cast_lt.mpr this
    have hnd : (↑n - ↑d : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hdlt)
    have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le d) (Nat.lt_of_succ_lt_succ hd)
    have hn1 : (↑n : ℝ) + 1 ≠ 0 := ne_of_gt (add_pos (Nat.cast_pos.mpr hnPos) one_pos)
    field_simp [hnd, hn1]
    ring
  · apply Subtype.ext
    simp only [Fraction.Fraction_coe, Fraction.ofPos_coe, unitInterval.coe_symm_eq,
      Nat.cast_add, Nat.cast_succ]
    have : d < n := Nat.lt_of_succ_lt_succ hd
    rw [Nat.cast_sub (le_of_lt this)]
    have hdlt : (↑d : ℝ) < ↑n := Nat.cast_lt.mpr this
    have hnd : (↑n - ↑d : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hdlt)
    have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le d) (Nat.lt_of_succ_lt_succ hd)
    have hn1 : (↑n : ℝ) + 1 ≠ 0 := ne_of_gt (add_pos (Nat.cast_pos.mpr hnPos) one_pos)
    field_simp [hnd, hn1]
    ring
/--
  When γ is a dipath, an we split it on the intervals [0, (d+1)/(n+1)] and [(d+1)/(n+1), 1], then the image of γ of
  [(i+d.succ)/(n+1), (i+d.succ+1)/(n+1)] is equal to the image the second part of γ of [i/(n-d), (i+1)/(n-d)].
-/
lemma secondPart_range_partial_interval_coe (γ : Dipath x₀ x₁) {i d n : ℕ} (hd : d.succ < n.succ) (hi : i < n - d) :
  (SecondPart γ (Fraction (Nat.succ_pos n) (le_of_lt hd))).extend '' Icc (↑i/(↑n-↑d)) ((↑i+1)/(↑n-↑d))
    = γ.extend ''  Icc ((↑(i+d.succ))/(↑n+1)) ((↑(i+d.succ) + 1)/(↑n+1)) := by
  have := secondPart_range_partial_interval γ hd hi
  rw [←Dipath.image_extend_eq_image] at this
  rw [←Dipath.image_extend_eq_image] at this
  convert this
  · exact (Nat.cast_sub (le_of_lt $ Nat.lt_of_succ_lt_succ hd)).symm
  · exact (Nat.cast_succ _).symm
  · exact (Nat.cast_sub (le_of_lt $ Nat.lt_of_succ_lt_succ hd)).symm
  · exact (Nat.cast_succ _).symm
  · exact (Nat.cast_succ _).symm
  · exact (Nat.cast_succ _).symm
/-! ### Mixed Parts -/
/--
  Splitting a dipath `γ` at `[0, k/n]` and then at `[0, 1/k]` is the same as splitting it at `[0, 1/n]`.
-/
lemma firstPart_of_firstPart (γ : Dipath x₀ x₁) {n k : ℕ} (hkn : k < n) (hk : 0 < k) :
    FirstPart
      (FirstPart γ (Fraction (lt_trans hk hkn) (le_of_lt hkn)))
        (Fraction.ofPos hk) -- 1/k
    = (FirstPart γ (Fraction.ofPos $ lt_trans hk hkn)).cast rfl
      (show γ _ = γ _ by { congr 1; rw [←Fraction.mul_inv hk (le_of_lt hkn)]; rfl }) := by
  ext x
  show γ _ = γ _
  congr 1
  rw [←Fraction.mul_inv hk (le_of_lt hkn)]
  simp
  rw [mul_assoc]
/--
  Splitting a dipath `[0, (k+1)/(n+1)]` and then `[1/(k+1), 1]` is the same as
  splitting it `[1/(n+1), 1]` and then `[0, k/n]`
-/
lemma first_part_of_second_part (γ : Dipath x₀ x₁) {n k : ℕ} (hkn : k < n) (hk : 0 < k) :
  SecondPart
    (FirstPart γ (Fraction (Nat.succ_pos n) (le_of_lt $ Nat.succ_lt_succ hkn))) -- (k+1)/(n+1)
    (Fraction.ofPos (Nat.succ_pos k)) -- 1/(k+1)
  =
  (FirstPart
      (SecondPart γ (Fraction.ofPos (Nat.succ_pos n))) -- 1/(n+1)
      (Fraction (lt_trans hk hkn) (le_of_lt hkn)) -- k/n
  ).cast
    (show γ _ = γ _ by congr 1; apply Subtype.coe_inj.mp; rw [←Fraction.mul_inv (Nat.succ_pos k) (le_of_lt (Nat.succ_lt_succ hkn))]; rfl)
    (show γ _ = γ _ by
      congr 1
      apply Subtype.ext
      simp only [Fraction.Fraction_coe, Fraction.ofPos_coe, unitInterval.coe_symm_eq,
        Nat.cast_succ]
      have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (lt_trans hk hkn))
      have hn1 : (n : ℝ) + 1 ≠ 0 := ne_of_gt (add_pos (Nat.cast_pos.mpr (lt_trans hk hkn)) one_pos)
      field_simp [hn0, hn1]
      ring)
    := by
  ext x
  show γ _ = γ _
  congr 1
  simp
  have : (k : ℝ) > 0 := Nat.cast_pos.mpr hk
  have : (n : ℝ) > 0 := Nat.cast_pos.mpr (lt_trans hk hkn)
  rw [←one_div]
  rw [←one_div]
  rw [FractionEqualities.one_sub_inverse_of_add_one _]
  rw [FractionEqualities.one_sub_inverse_of_add_one _]
  rw [mul_comm ((k : ℝ)/(↑k + 1)) (x : ℝ)]
  rw [mul_div, ← add_div, FractionEqualities.frac_cancel']
  rw [← mul_assoc ((n : ℝ) / (n+1 : ℝ)) (k/n : ℝ) (x : ℝ)]
  rw [FractionEqualities.frac_cancel']
  rw [mul_comm ((k : ℝ)/(↑n + 1)) (x : ℝ)]
  rw [mul_div, ← add_div]
  repeat { linarith }
/--
  Splitting a dipath [(k+2)/(n+2), 1] is the same as splitting it [1/(n+2), 1] and then [(k+1)/(n+1), 1]
-/
lemma second_part_of_second_part (γ : Dipath x₀ x₁) {n k : ℕ} (hkn : k < n) :
  SecondPart
    (SecondPart γ (Fraction.ofPos (Nat.succ_pos n.succ))) -- 1/(n+2)
    (Fraction (Nat.succ_pos n) (le_of_lt $ Nat.succ_lt_succ hkn)) -- (k+1)/(n+1)
  =
  (
    SecondPart γ (Fraction (Nat.succ_pos n.succ) (le_of_lt $ Nat.succ_lt_succ (Nat.succ_lt_succ hkn))) -- (k+2)/(n+2)
  ).cast
    (show γ _ = γ _ by
      congr 1
      apply Subtype.ext
      simp only [Fraction.Fraction_coe, Fraction.ofPos_coe, unitInterval.coe_symm_eq,
        Nat.cast_succ, Nat.cast_zero, Nat.cast_one]
      have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hkn
      have hn1 : (n : ℝ) + 1 ≠ 0 := ne_of_gt (add_pos (Nat.cast_pos.mpr hn) one_pos)
      have hn2 : (n : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
      field_simp [hn1, hn2]
      ring
    )
    rfl := by
  ext x
  show γ _ = γ _
  congr 1
  simp
  have : (n : ℝ) > 0 := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le k) hkn)
  -- Rewrite left side to ... / (n+1+1)
  rw [← one_div]
  rw [FractionEqualities.one_sub_inverse_of_add_one _]
  rw [FractionEqualities.one_sub_frac]
  rw [FractionEqualities.one_sub_frac]
  rw [mul_comm (((n : ℝ) - ↑k) / _) (x : ℝ)]
  rw [mul_div]
  rw [← add_div]
  rw [FractionEqualities.frac_cancel']
  rw [← add_div]
  -- Rewrite right side to ... / (n+1+1)
  rw [mul_comm _ (x : ℝ)]
  rw [mul_div]
  rw [← add_div]
  -- Show that numerators are equal
  congr 1
  ring
  repeat { linarith }
/-! ### Trans Parts -/
variable {x₂ : X}
/--
If `γ₁` and `γ₂` are two paths, then the first part of `γ₁.trans γ₂` split at `1/2` is `γ₁`
-/
lemma first_part_trans (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) :
    (FirstPart (γ₁.trans γ₂) (Fraction.ofPos two_pos)) =
      γ₁.cast rfl (Dipath.trans_eval_at_half γ₁ γ₂) := by
  ext t
  rw [first_part_apply, Dipath.trans_apply]
  simp [t.2.2]
/--
If `γ₁` and `γ₂` are two paths, then the second part of `γ₁.trans γ₂` split at `1/2` is `γ₂`
-/
lemma second_part_trans (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) :
    (SecondPart (γ₁.trans γ₂) (Fraction.ofPos two_pos)) =
    γ₂.cast (Dipath.trans_eval_at_half γ₁ γ₂) rfl := by
  ext t
  rw [second_part_apply, Dipath.trans_apply]
  have h_two : 2 * (2⁻¹ : ℝ) = 1 := by norm_num
  have ht : 2 * (2⁻¹ * (t : ℝ) + 2⁻¹) - 1 = ↑t
  · rw [mul_add]
    rw [←mul_assoc]
    rw [h_two]
    ring
  have : (1 - 2⁻¹ : ℝ) = 2⁻¹ := by norm_num
  simp [this]
  by_cases h : 2⁻¹ * (t : ℝ) ≤ 0
  · have : t = 0 := Subtype.coe_inj.mp (show (t : ℝ) = 0 by linarith [t.2.1])
    simp [h, this]
  · simp [h, ht]
/--
If `γ₁` and `γ₂` are two paths, then the first part of `γ₁.trans γ₂` split at `1/(2n + 2)` is the
same as `γ₁` split at `1/(n + 1)`.
-/
lemma trans_first_part (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) (t : I) :
    (FirstPart (γ₁.trans γ₂) (Fraction.ofPos (Nat.succ_pos (n + n).succ))) t =
      (FirstPart γ₁ (Fraction.ofPos (Nat.succ_pos n))) t := by
  rw [first_part_apply]
  rw [first_part_apply]
  rw [Dipath.trans_apply]
  simp
  have : (n + n + 1 + 1 : ℝ) ≥ 2
  · rw [←Nat.cast_add]
    have : (↑(n + n) : ℝ) ≥ 0 := Nat.cast_nonneg (n + n)
    linarith
  have h₁ : (n + n + 1 + 1 : ℝ)⁻¹ ≤ 2⁻¹ := (inv_le_inv₀ (by linarith) two_pos).2 this
  have : (n + n + 1 + 1 : ℝ)⁻¹ * ↑t ≤ 2⁻¹
  · rw [← mul_one (2⁻¹ : ℝ)]
    apply mul_le_mul h₁ t.2.2 t.2.1
    norm_num
  rw [dif_pos this]
  apply congr_arg
  ext
  simp
  rw [←mul_assoc]
  congr 1
  have : (n + n + 1 + 1 : ℝ)  = (2 * (n + 1)) := by ring
  rw [this]
  rw [mul_inv]
  rw [←mul_assoc]
  norm_num
namespace AuxEqualities
lemma h₁ (t : I) : 0 ≤ (t : ℝ) := t.2.1
lemma h₂ (n : ℕ) : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
lemma h₃ (n : ℕ) : (n + 1 + 1 : ℝ) ≠ 0 := by linarith [h₂ n]
lemma h₄ (n : ℕ) : (↑n + ↑n + 1 + 1 + 1 + 1 : ℝ) > 0 := by linarith [h₂ n]
lemma h₅ (n : ℕ) : (↑n + ↑n + 1 + 1 + 1 + 1 : ℝ) = 2 * (↑n + 1 + 1) := by ring
lemma h₆ (n : ℕ) : (↑n + 1 + 1 : ℝ) / (↑n + ↑n + 1 + 1 + 1 + 1) = 2⁻¹ := by
  rw [h₅ n]
  rw [mul_comm]
  rw [div_mul_eq_div_div]
  rw [div_self (h₃ n)]
  exact one_div _
lemma h₇ (n : ℕ) : (n + n + 1 + 1 + 1: ℝ) ≠ 0 := by linarith [h₂ n]
lemma h₈ (n : ℕ) : (↑n + 1 + (↑n + 1) + 1 + 1 : ℝ) = (↑n + ↑n + 1 + 1 + 1 + 1) := by ring
lemma e₁ (n : ℕ) (t : I) :
    (1 - (n + 1 : ℝ) / (↑n + 1 + 1)) * ↑t + (↑n + 1) / (↑n + 1 + 1) =
    ((t : ℝ) + ↑n + 1) / (↑n + 1 + 1) := by
  nth_rewrite 1 [←div_self (h₃ n)]
  ring
lemma e₂ (n : ℕ) (t : I) :
    ((1 - (n + n + 1 + 1 : ℝ) / (↑n + ↑n + 1 + 1 + 1)) * ↑t + (↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1)) =
    (↑t + ↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1) := by
  nth_rewrite 1 [←div_self (h₇ n)]
  ring
lemma e₃ (n : ℕ) :
    (1 - (n + 1 + (n + 1) + 1 + 1 : ℝ)⁻¹) =
    (↑n + ↑n + 1 + 1 + 1) / (↑n + ↑n + 1 + 1 + 1 + 1) := by
  nth_rewrite 1 [←div_self (ne_of_gt (h₄ n))]
  ring_nf
lemma e₄ (n : ℕ) (t : I) :
    ((↑n + ↑n + 1 + 1 + 1 : ℝ) / (↑n + ↑n + 1 + 1 + 1 + 1) * ((↑t + ↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1))) =
    (↑t + ↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1 + 1) := by
  rw [mul_comm]
  rw [div_mul_div_cancel₀ (h₇ n)]
lemma e₅ (n : ℕ) (r : ℝ) :
    2 * (r / (n + n + 1 + 1 + 1 + 1 : ℝ) + ((n : ℝ) + 1 + (↑n + 1) + 1 + 1)⁻¹) =
    (r + 1) / (↑n + 1 + 1) := by
  rw [h₈]
  rw [← one_div]
  rw [div_add_div_same]
  rw [h₅]
  rw [mul_div]
  rw [mul_comm]
  rw [← mul_div]
  rw [div_mul_eq_div_div]
  rw [div_self (show (2 : ℝ) ≠ 0 by norm_num)]
  ring
lemma e₆ (n : ℕ) (r : ℝ) :
  (1 - (n + 1 + 1 : ℝ)⁻¹) * r + (n + 1 + 1 : ℝ)⁻¹ = ((n + 1) * r + 1) / (n + 1 + 1) := by
  nth_rewrite 1 [←div_self (h₃ n)]
  ring
end AuxEqualities
open AuxEqualities
/--
If `γ₁` and `γ₂` are two paths, then
  `γ₁.trans γ₂` --> `[1/(2n + 4), 1]` --> `[0, (2n + 2)/(2n + 3)]` (so taking `[1/(2n + 4), (2n + 3)/(2n + 4)]`)
is the same as
  `γ₁` --> `[1/(n+2), 1]`, added to `γ₂` --> `[0, (n+1)/(n+2)]`
-/
lemma trans_first_part_of_second_part (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) (t : I) :
  (FirstPart
    (SecondPart (γ₁.trans γ₂) (Fraction.ofPos $ Nat.succ_pos (n.succ + n.succ).succ))
    (Fraction (Nat.succ_pos (n + n).succ.succ) (le_of_lt (Nat.lt_succ_self ((n + n).succ.succ))))
   ) t
  =
  ((SecondPart γ₁ (Fraction.ofPos (Nat.succ_pos n.succ)))).trans
   (FirstPart γ₂ (Fraction (Nat.succ_pos n.succ) (Nat.le_succ n.succ))) t := by
  rw [first_part_apply, second_part_apply, Dipath.trans_apply, Dipath.trans_apply]
  have : (n : ℝ) + ↑n + 2 + 1 = ↑n + ↑n + 1 + 1 + 1 := by ring
  split_ifs with h ht ht
  · rw [second_part_apply]
    apply congr_arg
    simp
    rw [e₃, mul_comm _ (t : ℝ), mul_div]
    rw [mul_comm (_/_) (_/_)]
    rw [this]
    rw [div_mul_div_cancel₀ (h₇ n)]
    rw [e₆]
    rw [e₅]
    ring
  · exfalso
    revert h
    apply not_le.mpr
    simp
    rw [e₃]
    rw [mul_comm _ (t : ℝ)]
    rw [mul_div]
    rw [mul_comm (_/_) (_/_)]
    rw [this]
    rw [div_mul_div_cancel₀ (h₇ n)]
    apply (mul_lt_mul_iff_of_pos_left (show 0 < (2 : ℝ) by norm_num)).mp
    rw [e₅]
    apply (lt_div_iff₀ (show (n + 1 + 1 : ℝ) > 0 by linarith [h₂ n])).mpr
    norm_num
    push_neg at ht
    calc (n + 1 : ℝ)
      _ = 1 * (n + 1 : ℝ) := by rw [one_mul]
      _ = (2⁻¹ * 2) * (n + 1 : ℝ) := by norm_num
      _ = 2⁻¹ * (n + n + 1 + 1 : ℝ) := by ring
      _ = 1/2 * (n + n + 1 + 1 : ℝ) := by rw [one_div]
      _ < t * (n + n + 1 + 1 : ℝ) := mul_lt_mul_of_pos_right ht (by linarith [h₂ n])
  · exfalso
    revert h
    apply imp_false.mpr
    apply not_not.mpr
    simp
    rw [e₃, mul_comm _ (t : ℝ), mul_div, mul_comm (_/_) (_/_)]
    rw [this]
    rw [div_mul_div_cancel₀ (h₇ n)]
    apply (mul_le_mul_iff_of_pos_left (show 0 < (2 : ℝ) by norm_num)).mp
    rw [e₅]
    apply (div_le_iff₀ (show (n + 1 + 1 : ℝ) > 0 by linarith [h₂ n])).mpr
    norm_num
    calc ↑t * (n + n + 1 + 1 : ℝ)
      _ ≤ 1/2 * (n + n + 1 + 1 : ℝ) := mul_le_mul_of_nonneg_right ht (le_of_lt (by linarith [h₂ n]))
      _ = (1/2 * 2) * (n + 1 : ℝ)   := by ring
      _ = 1 * (n + 1 : ℝ)           := by rw [div_mul_cancel₀ (1 : ℝ) (show (2 : ℝ) ≠ 0 by norm_num)]
      _ = (n + 1 : ℝ)               := by rw [one_mul]
  · rw [first_part_apply]
    apply congr_arg
    simp
    rw [e₃]
    rw [mul_comm _ (t : ℝ)]
    rw [mul_div]
    rw [mul_comm (_/_) (_/_)]
    rw [this]
    rw [div_mul_div_cancel₀ (h₇ n)]
    rw [e₅]
    nth_rewrite 6 [←div_self (h₃ n)]
    ring
/--
If `γ₁` and `γ₂` are two paths, then
  `γ₁.trans γ₂` --> `[1/(2n + 4), 1]` --> `[(2n+2)/(2n+3), 1]` (so to `[(2n+3)/(2n+4), 1]`)
is the same as
  `γ₂` --> `[(n+1)/(n+2), 1]`
-/
lemma trans_second_part_second_part (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) (t : I) :
  (SecondPart
    (SecondPart (γ₁.trans γ₂) $ Fraction.ofPos $ Nat.succ_pos (n.succ + n.succ).succ)
    (Fraction (Nat.succ_pos (n + n).succ.succ) (Nat.le_succ (n + n).succ.succ))
   ) t
  =
    (SecondPart γ₂ (Fraction (Nat.succ_pos n.succ) (Nat.le_succ n.succ))) t := by
  rw [second_part_apply]
  rw [second_part_apply]
  rw [second_part_apply]
  rw [Dipath.trans_apply]
  simp
  have : (n : ℝ) + ↑n + 2 = ↑n + ↑n + 1 + 1 := by ring
  split_ifs with h
  · exfalso
    rw [this] at h
    rw [e₂] at h
    rw [e₃] at h
    rw [e₄] at h
    rw [←one_div] at h
    rw [h₈] at h
    rw [div_add_div_same] at h
    have : (↑n + 1 + 1 : ℝ) < (↑t + ↑n + ↑n + 1 + 1 + 1) := by linarith [h₂ n, h₁ t]
    have := lt_of_lt_of_le ((div_lt_div_iff_of_pos_right (h₄ n)).2 this) h
    rw [h₆] at this
    exact lt_irrefl _ this
  apply congr_arg
  simp
  rw [this]
  rw [e₁, e₂, e₃, e₄, e₅]
  nth_rewrite 6 [←div_self (h₃ n)]
  rw [div_sub_div_same]
  ring
/--
If `γ₁` and `γ₂` are two paths, then `γ₁.trans γ₂` evaluated at `1/(2n+2)` is the same as
`γ₁` evaluated at `1/(n+1)`.
-/
lemma trans_image_inv_eq_first (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) :
    (γ₁.trans γ₂) (Fraction.ofPos (Nat.succ_pos (n + n).succ)) =
      γ₁ (Fraction.ofPos (Nat.succ_pos n)) := by
  have := trans_first_part γ₁ γ₂ n 1
  rw [SplitDipath.first_part_apply] at this
  rw [SplitDipath.first_part_apply] at this
  convert this using 2 <;>
    (apply Subtype.ext <;> simp [Fraction.ofPos_coe] <;> ring)
/--
If `γ₁` and `γ₂` are two paths, then `γ₁.trans γ₂` --> `[1/(2n+4), 1]` evaluated at `(2n+2)/(2n+3)` is the same as
`γ₂` evaluated at `(n+1)/(n+2)`.
-/
lemma second_part_trans_eval_at_end (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) :
    (SecondPart (γ₁.trans γ₂) $ Fraction.ofPos $ Nat.succ_pos (n.succ + n.succ).succ)
    (Fraction (Nat.succ_pos (n+n).succ.succ) (le_of_lt (Nat.lt_succ_self _)))
    = γ₂ (Fraction (Nat.succ_pos (n.succ)) (le_of_lt (Nat.lt_succ_self _))) := by
  rw [second_part_apply]
  rw [Dipath.trans_apply]
  have : (n : ℝ) + ↑n + 2 = ↑n + ↑n + 1 + 1 := by ring
  rw [dif_neg]
  · apply congr_arg
    simp
    apply Subtype.ext
    simp only [unitInterval.coe_symm_eq]
    rw [e₃]
    rw [mul_comm (_ / _) (_ / _)]
    rw [this]
    rw [div_mul_div_cancel₀ (h₇ n)]
    rw [e₅ n (↑n + ↑n + 1 + 1)]
    nth_rewrite 6 [←div_self (h₃ n)]
    field_simp [h₃ n]
    push_cast
    ring
  simp
  rw [e₃]
  rw [mul_comm]
  rw [this]
  rw [div_mul_div_cancel₀ (h₇ n)]
  rw [h₈]
  rw [← one_div (n + n + 1 + 1 + 1 + 1 : ℝ)]
  rw [div_add_div_same]
  apply (lt_div_iff₀ (h₄ n)).mpr
  rw [h₅]
  rw [←mul_assoc]
  norm_num
  linarith [h₂ n]
end SplitProperties
end
end Lean4_SplitPath_split_properties
/-! Source module: Lean4.path_cover -/
section Lean4_path_cover
/-
  This file contains the definition of a directed path being n-covered by two subspaces X₁ and X₂:
  It maps any subinterval [i/n, (i+1)/n] into either X₁ or X₂.
  We give this definition inductively.
  This file contains properties about dipaths and parts of dipaths being n-covered.
-/
open Set
open scoped unitInterval
noncomputable section
namespace Dipath
variable {X : dTopCat} {X₀ X₁ : Set X}
def covered {x₀ x₁ : X} (_ : X₀ ∪ X₁ = univ) (γ : Dipath x₀ x₁) : Prop :=
  (range γ ⊆ X₀) ∨ (range γ ⊆ X₁)
namespace covered
variable {x₀ x₁ : X}
lemma covered_refl (x : X) (hX : X₀ ∪ X₁ = univ) : covered hX (Dipath.refl x) := by
  cases ((Set.mem_union x X₀ X₁).mp (Filter.mem_top.mpr hX x))
  case inl hx₀ => left; exact DiSubtype.range_refl_subset_of_mem hx₀
  case inr hx₁ => right; exact DiSubtype.range_refl_subset_of_mem hx₁
lemma covered_of_extended_image_subset (γ : Dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ) (hγ : γ.extend '' I ⊆ X₀ ∨ γ.extend '' I ⊆ X₁) :
    covered hX γ := by
  rw [(Dipath.range_eq_image γ).symm] at hγ
  exact hγ
lemma covered_of_covered_trans {x₂ : X} {γ₁: Dipath x₀ x₁} {γ₂ : Dipath x₁ x₂}
  {hX : X₀ ∪ X₁ = univ} (hγ : covered hX (γ₁.trans γ₂)):
    (covered hX γ₁ ∧ covered hX γ₂) := by
  unfold covered at *
  rw [Dipath.trans_range _ _] at hγ
  cases hγ
  case inl h =>
    constructor
    · exact Or.inl $ subset_trans subset_union_left h
    · exact Or.inl $ subset_trans subset_union_right h
  case inr h =>
    constructor
    · exact Or.inr $ subset_trans subset_union_left h
    · exact Or.inr $ subset_trans subset_union_right h
lemma covered_subparam_of_covered {γ : Dipath x₀ x₁} {hX : X₀ ∪ X₁ = univ} (hγ : covered hX γ) (f : D(I, I)) :
    covered hX (γ.subparam f) := by
  cases hγ
  case inl hγ =>
    exact Or.inl (subset_trans (Dipath.subparam_range γ f) hγ)
  case inr hγ =>
    exact Or.inr (subset_trans (Dipath.subparam_range γ f) hγ)
lemma covered_reparam_iff (γ : Dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    covered hX γ ↔ covered hX (γ.reparam f hf₀ hf₁) := by
  unfold covered
  rw [Dipath.range_reparam _ _]
lemma covered_cast_iff {x₀' x₁' : X}  (γ : Dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) :
    covered hX γ ↔ covered hX (γ.cast hx₀ hx₁) := by rfl
/--
 If γ is a dipath that is covered, then by splitting it into two parts [0, T] and [T, 1], both parts remain covered
-/
lemma covered_split_path {γ : Dipath x₀ x₁} {hX : X₀ ∪ X₁ = Set.univ} {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) (hγ : covered hX γ):
    covered hX (SplitDipath.FirstPart γ T) ∧ covered hX (SplitDipath.SecondPart γ T) := by
  apply covered_of_covered_trans
  apply (covered_reparam_iff _ hX (SplitDipath.trans_reparam_map hT₀ hT₁) _ _).mpr
  rw [SplitDipath.first_trans_second_reparam_eq_self γ hT₀ hT₁] at hγ
  exact hγ
end covered
open covered
/--
We say that `covered_partwise hX γ n` if a dipath γ can be split into n+1 parts, each of which is covered by `X₁` or `X₂`
-/
def covered_partwise (hX : X₀ ∪ X₁ = Set.univ) {x y : X} (γ : Dipath x y) (n : ℕ) : Prop :=
  match n with
  | Nat.zero => covered hX γ
  | Nat.succ n => covered hX (SplitDipath.FirstPart γ (Fraction.ofPos (show 0 < (n.succ + 1) by norm_num))) ∧
      covered_partwise hX (SplitDipath.SecondPart γ (Fraction.ofPos (show 0 < (n.succ + 1) by norm_num))) n
namespace covered_partwise
lemma covered_partwise_of_equal (hX : X₀ ∪ X₁ = Set.univ) {x₀ x₁ : X} {γ₁ γ₂ : Dipath x₀ x₁} {n m : ℕ} (h : γ₁ = γ₂) (h' : n = m) (hγ₁ : covered_partwise hX γ₁ n) :
  covered_partwise hX γ₂ m := by subst_vars; exact hγ₁
/--
 If γ is a dipath that is fully covered, then it is also partwise covered for all n ∈ ℕ
-/
lemma covered_partwise_of_covered {hX : X₀ ∪ X₁ = Set.univ} (n : ℕ) :
    ∀ {x₀ x₁ : X} {γ : Dipath x₀ x₁}, covered hX γ → covered_partwise hX γ n := by
  induction n
  case zero =>
    intros _ _ _ hγ
    exact hγ
  case succ n ih =>
    intros x₀ x₁ γ hγ
    constructor
    · exact (covered_split_path (Fraction.ofPos_pos _) (Fraction.ofPos_lt_one (by norm_num)) hγ).left
    · apply ih
      exact (covered_split_path (Fraction.ofPos_pos _) (Fraction.ofPos_lt_one (by norm_num)) hγ).right
lemma covered_partwise_cast_iff  (hX : X₀ ∪ X₁ = univ) {n : ℕ} :
    ∀ {x₀ x₁ x₀' x₁' : X} (γ : Dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁),
    covered_partwise hX γ n ↔ covered_partwise hX (γ.cast hx₀ hx₁) n := by
  induction n
  case zero =>
    intros x₀ x₁ x₀' x₁' γ hx₀ hx₁
    exact covered_cast_iff _ _ _ _
  case succ n ih =>
    intros x₀ x₁ x₀' x₁' γ hx₀ hx₁
    unfold covered_partwise
    rw [SplitProperties.firstPart_cast, SplitProperties.secondPart_cast]
    constructor
    · rintro ⟨hγ₁, hγ₂⟩
      constructor
      · exact (covered_cast_iff _ _ _ _).mp hγ₁
      · exact (ih _ _ _).mp hγ₂
    · rintro ⟨hγ₁, hγ₂⟩
      constructor
      · exact (covered_cast_iff _ _ _ _).mpr hγ₁
      · exact (ih _ _ _).mpr hγ₂
/--
 A dipath γ that can be covered with n+1 intervals can satisfied `covered_partwise _ γ n`.
 This is the converse of `covered_by_intervals_of_covered_partwise`.
-/
lemma covered_partwise_of_covered_by_intervals {hX : X₀ ∪ X₁ = Set.univ} (n : ℕ) :
    ∀ {x₀ x₁ : X} {γ : Dipath x₀ x₁}, (∀ (i : ℕ) (h : i < (n+1)),
      γ.extend '' Set.Icc ((↑i)/(↑n+1)) ((↑i+1)/(↑n+1)) ⊆ X₀ ∨
      γ.extend '' Set.Icc ((↑i)/(↑n+1)) ((↑i+1)/(↑n+1)) ⊆ X₁) → covered_partwise hX γ n := by
  induction n
  case zero =>
    intros x₀ x₁ γ hγ
    have := hγ 0 (by linarith)
    unfold covered_partwise covered
    rw [Dipath.range_eq_image]
    convert this <;> simp
  case succ n ih =>
    intros x₀ x₁ γ hγ
    constructor
    · unfold covered
      rw [SplitProperties.firstPart_range_interval γ _, ←Dipath.image_extend_eq_image]
      convert hγ 0 (by norm_num) <;> norm_num
    · apply ih
      intros i hi
      have : i + 1 < n + 2 := by linarith
      have h := hγ (i+1) (this)
      suffices :
        (SplitDipath.SecondPart γ _).extend '' Set.Icc (↑i/(↑(n+1))) ((↑i+1)/(↑(n+1))) ⊆ X₀ ∨
        (SplitDipath.SecondPart γ _).extend '' Set.Icc (↑i/(↑(n+1))) ((↑i+1)/(↑(n+1))) ⊆ X₁
      · convert this <;> exact (Nat.cast_succ n).symm
      rw [SplitProperties.secondPart_range_interval_coe γ _ _]
      convert h <;> exact (Nat.cast_succ i).symm
      · exact hi
      · exact Nat.succ_pos n
/--
 A dipath γ that satisfies `covered_partwise _ γ n` can be covered with n+1 intervals.
 This is the converse of `covered_partwise_of_covered_by_intervals`.
-/
lemma covered_by_intervals_of_covered_partwise {hX : X₀ ∪ X₁ = Set.univ} (n : ℕ) :
    ∀ {x₀ x₁ : X} {γ : Dipath x₀ x₁}, covered_partwise hX γ n → (∀ (i : ℕ) (h : i < (n+1)),
      γ.extend '' Set.Icc ((↑i)/(↑n+1)) ((↑i+1)/(↑n+1)) ⊆ X₀ ∨
      γ.extend '' Set.Icc ((↑i)/(↑n+1)) ((↑i+1)/(↑n+1)) ⊆ X₁) := by
  induction n
  case zero =>
    intros x₀ x₁ γ hγ i hi
    rw [show i = 0 by linarith]
    suffices : γ.extend '' I ⊆ X₀ ∨ γ.extend '' I ⊆ X₁
    · convert this <;> simp
    rw [←Dipath.range_eq_image γ]
    exact hγ
  case succ n ih =>
    intros x₀ x₁ γ hγ i hi
    by_cases h_i_eq_0 : i = 0
    · have hγ_first_cov := hγ.left
      rw [h_i_eq_0]
      have := SplitProperties.firstPart_range_interval_coe γ (show 0 < n+2 by linarith)
      unfold covered at hγ_first_cov
      rw [this] at hγ_first_cov
      convert hγ_first_cov <;> simp
      ring
      ring
    · suffices : γ.extend '' Icc ((↑(i-1) + 1)/(↑(n.succ) + 1)) ((↑(i-1) + 1 + 1)/(↑(n.succ) + 1)) ⊆ X₀ ∨
              γ.extend '' Icc ((↑(i-1) + 1)/(↑(n.succ) + 1)) ((↑(i-1) + 1 + 1)/(↑(n.succ) + 1)) ⊆ X₁
      · convert this <;> rw [Nat.cast_sub (Nat.pos_of_ne_zero h_i_eq_0)] <;> simp
      have : i - 1 < n.succ := Nat.lt_of_succ_lt_succ ((Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h_i_eq_0)).symm ▸ hi)
      rw [←SplitProperties.secondPart_range_interval_coe γ (this) (by linarith)]
      convert ih hγ.right (i-1) (this) <;> exact (Nat.cast_succ n)
/--
  Let γ be a dipath covered by n+1 parts. Let 0 < k < n+1 be given. Then the first part
  of γ, split by k/(n+1) is covered by k parts.
  Here, k = d.succ, so we don't need the requirement k > 0.
-/
lemma covered_partwise_first_part_d (hX : X₀ ∪ X₁ = Set.univ) {n d : ℕ} (hd_n : d.succ < n.succ) :
    ∀ {x₀ x₁ : X} {γ : Dipath x₀ x₁} (_ : covered_partwise hX γ n),
      covered_partwise hX (SplitDipath.FirstPart γ $ Fraction (Nat.succ_pos n) (le_of_lt hd_n)) d := by
  intro x y γ hγ
  apply covered_partwise_of_covered_by_intervals
  intro i hi
  rw [SplitProperties.firstPart_range_interval_partial_coe γ hd_n hi]
  exact covered_by_intervals_of_covered_partwise n hγ i (lt_trans hi hd_n)
/--
  Input: (d+1) < (n+1) --> split at (d+1)/(n+1)
  Let γ be a dipath covered by n+1 parts. Let 0 < k < n+1 be given. Then the second part
  of γ, split by k/(n+1) is covered by n+1-k parts.
  Here, k = d.succ, so we don't need the requirement k > 0.
-/
lemma covered_partwise_second_part_d (hX : X₀ ∪ X₁ = Set.univ) {n d : ℕ} (hd_n : d.succ < n.succ) :
    ∀ {x₀ x₁ : X} {γ : Dipath x₀ x₁} (_ : covered_partwise hX γ n),
    covered_partwise hX (SplitDipath.SecondPart γ $ Fraction (Nat.succ_pos n) (le_of_lt hd_n)) (n - d.succ) := by
  intros x y γ hγ
  apply covered_partwise_of_covered_by_intervals
  intros i hi
  rw [←Nat.cast_succ]
  have hi_lt_n_sub_d : i < n - d := by
    convert hi using 1
    rw [Nat.sub_succ]
    exact (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hd_n))).symm
  have : i + d.succ < n + 1 := by
    rw [Nat.add_succ]
    apply Nat.succ_lt_succ
    exact lt_tsub_iff_right.mp hi_lt_n_sub_d
  have := covered_by_intervals_of_covered_partwise n hγ (i + d.succ) this
  rw [←SplitProperties.secondPart_range_partial_interval_coe γ hd_n hi_lt_n_sub_d] at this
  have h : (n-d.succ).succ = n - d := by
    rw [Nat.sub_succ]
    exact Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hd_n))
  convert this <;> rw [h] <;> exact Nat.cast_sub (le_of_lt $ Nat.lt_of_succ_lt_succ hd_n)
/--
  Let γ be a dipath covered by n+2 parts. Then the first part of γ, split by (n+1)/(n+2) is covered by n+1 parts.
-/
lemma covered_partwise_first_part_end_split (hX : X₀ ∪ X₁ = Set.univ) {n : ℕ} {x₀ x₁ : X}
  {γ : Dipath x₀ x₁} (hγ : covered_partwise hX γ n.succ) :
    covered_partwise hX (SplitDipath.FirstPart γ $ Fraction (Nat.succ_pos n.succ) (Nat.le_succ n.succ)) n :=
  covered_partwise_first_part_d hX (Nat.lt_succ_self _) hγ
/--
  Let γ be a dipath covered by n+2 parts. Then the second part of γ, split by (n+1)/(n+2) is covered
-/
lemma covered_second_part_end_split (hX : X₀ ∪ X₁ = Set.univ) {n : ℕ} {x₀ x₁ : X}
  {γ : Dipath x₀ x₁} (hγ : covered_partwise hX γ n.succ) :
    covered hX (SplitDipath.SecondPart γ $ Fraction (Nat.succ_pos n.succ) (Nat.le_succ n.succ)) := by
  have := covered_partwise_second_part_d hX (Nat.lt_succ_self n.succ) hγ
  rw [Nat.sub_self n.succ] at this
  exact this
/--
  Let γ be a dipath and n ≥ 2:
  If the first part [0, 1/(n+1)] can be covered with k intervals and the second part [1/(n+1), 1] can be covered with k*n intervals,
  then the entire path can be covered with k*(n+1) intervals.
-/
lemma covered_partwise_of_parts (hX : X₀ ∪ X₁ = Set.univ) {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k > 0) :
  Π {x₀ x₁ : X} {γ : Dipath x₀ x₁},
    ((covered_partwise hX (SplitDipath.FirstPart γ (Fraction.ofPos (Nat.succ_pos n))) (k - 1)) ∧
    (covered_partwise hX (SplitDipath.SecondPart γ (Fraction.ofPos (Nat.succ_pos n))) (n * k - 1))) →
    (covered_partwise hX γ ((n + 1) * k - 1)) := by
  rintro x₀ x₁ γ ⟨hγ_first, hγ_second⟩
  apply covered_partwise_of_covered_by_intervals
  intros i hi
  have prod_pos : (n + 1) * k > 0 := mul_pos (Nat.succ_pos n) hk
  set d' := k - 1 with d_def
  set n' := (n + 1) * k - 1 with n_def
  have hd_eq_k : d'.succ = k := by rw [d_def, ←Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos hk]
  have h₁ : d'.succ < n'.succ := by
    rw [n_def, hd_eq_k, ←Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos prod_pos]
    nth_rewrite 1 [←one_mul k]
    exact (mul_lt_mul_iff_of_pos_right hk).mpr (by linarith)
  have : Fraction (Nat.succ_pos n') (le_of_lt h₁) = Fraction.ofPos (Nat.succ_pos n) := by
    apply Subtype.ext
    rw [Fraction.Fraction_coe, Fraction.ofPos_coe, hd_eq_k]
    have hn'_succ : n'.succ = (n + 1) * k := by
      rw [n_def, ← Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos prod_pos]
    rw [hn'_succ]
    push_cast
    have hk_real : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
    field_simp
    <;> ring
  have h₃ : (n' : ℝ) - (d' : ℝ) = (↑(n * k - 1) : ℝ) + 1 := by
    rw [←Nat.cast_sub (le_of_lt $ Nat.lt_of_succ_lt_succ h₁), ←Nat.cast_succ, ← Nat.pred_eq_sub_one]
    rw [Nat.succ_pred_eq_of_pos (Nat.mul_pos hn hk), n_def, d_def, Nat.sub_sub, add_comm 1 (k-1)]
    rw [Nat.add_one (k-1), Nat.sub_one k, Nat.succ_pred_eq_of_pos hk, add_mul, one_mul]
    rw [Nat.add_sub_assoc (le_refl k), Nat.sub_self]
    rfl
  by_cases h : i < k
  · -- Use the covering of the first part of γ
    have h₂ : i < d'.succ := by
      rw [d_def, ←Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos hk]
      exact h
    rw [←SplitProperties.firstPart_range_interval_partial_coe γ h₁ h₂]
    convert (covered_by_intervals_of_covered_partwise (k-1) hγ_first i (by linarith))
  · push_neg at h
    set i' := i - d'.succ with i_def
    have h₂ : i' < n' - d' := by
      rw [i_def, ←Nat.succ_sub_succ n' d']
      have : d'.succ ≤ i := hd_eq_k.symm ▸ h
      apply (tsub_lt_tsub_iff_right this).mpr _
      exact hi
    have : i = i' + d'.succ := by
      rw [i_def, Nat.sub_add_cancel]
      exact hd_eq_k.symm ▸ h
    rw [this]
    have : i - k < n * k - 1 + 1 := by
      rw [Nat.sub_one (n * k), Nat.add_one (n * k).pred, Nat.succ_pred_eq_of_pos (mul_pos hn hk)]
      apply (tsub_lt_iff_right h).mpr _
      nth_rewrite 2 [←one_mul k]
      rw [←add_mul, ←Nat.succ_pred_eq_of_pos prod_pos]
      convert hi using 1
    rw [←SplitProperties.secondPart_range_partial_interval_coe γ h₁ h₂]
    convert (covered_by_intervals_of_covered_partwise (n * k - 1) hγ_second (i - k) this)
/--
  If a dipath γ can be covered in n+1 parts, it can also be covered in (k+1) * (n+1) parts
-/
lemma covered_partwise_refine (hX : X₀ ∪ X₁ = Set.univ) (n k : ℕ) :
    Π {x₀ x₁ : X} {γ : Dipath x₀ x₁}, covered_partwise hX γ n → covered_partwise hX  γ ((n + 1) * (k + 1) - 1) := by
  induction n
  case zero =>
    intros x₀ x₁ γ hγ
    exact covered_partwise_of_covered ((0+1)*(k+1)-1) hγ
  case succ n ih =>
    rintro x₀ x₁ γ ⟨hγ_cov_first, hγ_split_cov_second⟩
    apply covered_partwise_of_parts hX (Nat.succ_pos n) (Nat.succ_pos k)
    constructor
    · exact covered_partwise_of_covered k hγ_cov_first
    · convert ih hγ_split_cov_second
lemma covered_partwise_trans  {hX : X₀ ∪ X₁ = Set.univ} {n : ℕ} {x₀ x₁ x₂ : X} {γ₁ : Dipath x₀ x₁}
  {γ₂ : Dipath x₁ x₂} (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ n) :
    covered_partwise hX (γ₁.trans γ₂) (n + n).succ := by
  apply covered_partwise_of_covered_by_intervals
  intros i hi
  have h_lt : n.succ < (n + n).succ.succ := by linarith
  have h₁ : Fraction (Nat.succ_pos (n + n).succ) (le_of_lt h_lt) = Fraction.ofPos two_pos := by
    apply Subtype.ext
    rw [Fraction.Fraction_coe, Fraction.ofPos_coe]
    push_cast
    field_simp
    <;> ring
  by_cases h : i < n.succ
  · rw [←SplitProperties.firstPart_range_interval_partial_coe (γ₁.trans γ₂) h_lt h]
    rw [SplitProperties.firstPart_eq_of_split_point_eq (γ₁.trans γ₂) h₁]
    rw [SplitProperties.first_part_trans γ₁ γ₂]
    rw [Dipath.cast_image, Dipath.cast_image]
    exact covered_by_intervals_of_covered_partwise n hγ₁ i h
  · set k := i - n.succ with k_def
    push_neg at h
    rw [show i = k + n.succ by rw [k_def, Nat.sub_add_cancel]; exact h]
    have hn : (n + n).succ - n = n.succ := by rw [Nat.succ_sub, Nat.add_sub_cancel]; exact Nat.le_add_right n n
    have hn' : (↑(n + n).succ : ℝ) - ↑n = ↑n + 1 := by
      rw [←Nat.cast_succ n, ←hn, Nat.cast_sub]
      exact le_of_lt (Nat.lt_of_succ_lt_succ h_lt)
    have : i < n.succ + n.succ := by linarith
    have hk : k < n.succ := k_def ▸ (tsub_lt_iff_left h).mpr this
    have hk' : k < (n + n).succ - n := hn.symm ▸ hk
    rw [←SplitProperties.secondPart_range_partial_interval_coe (γ₁.trans γ₂) h_lt hk']
    rw [SplitProperties.secondPart_eq_of_split_point_eq (γ₁.trans γ₂) h₁]
    rw [SplitProperties.second_part_trans γ₁ γ₂]
    rw [Dipath.cast_image, Dipath.cast_image, hn']
    exact covered_by_intervals_of_covered_partwise n hγ₂ k hk
lemma has_interval_division {X₁ X₂ : Set X} (hX : X₁ ∪ X₂ = Set.univ) (X₁_open : IsOpen X₁)
  (X₂_open : IsOpen X₂) (γ : Dipath x₀ x₁) :
    ∃ (n : ℕ), (n > 0) ∧ ∀ (i : ℕ) (_ : i < n),
      Set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) ⊆ γ.extend ⁻¹' X₁ ∨
      Set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) ⊆ γ.extend ⁻¹' X₂ := by
  set c : ℕ → Set ℝ := fun i => if i = 0 then γ.extend ⁻¹' X₁ else γ.extend ⁻¹'  X₂ with c_def
  have h₁ : ∀ i, IsOpen (c i) := by
    intro i
    rw [c_def]
    by_cases i = 0
    case pos h =>
      simp [h]
      exact (Path.continuous_extend γ.toPath).isOpen_preimage X₁ X₁_open
    case neg h =>
      simp [h]
      exact (Path.continuous_extend γ.toPath).isOpen_preimage X₂ X₂_open
  have h₂ : I ⊆ ⋃ (i : ℕ), c i := by
    intros x _
    simp [c_def]
    have : γ.extend x ∈ X₁ ∪ X₂ := hX.symm ▸ (Set.mem_univ $ γ.extend x)
    cases this
    case inl h => use 0; simp; exact h
    case inr h => use 1; simp; exact h
  rcases (lebesgue_number_lemma_unit_interval h₁ h₂) with ⟨n, n_pos, hn⟩
  use n
  constructor
  · exact n_pos
  · intros i hi
    cases (hn i hi)
    rename_i j hj
    rw [c_def] at hj
    simp at hj
    by_cases j = 0
    case pos h => left; convert hj; simp [h]
    case neg h => right; convert hj; simp [h]
/--
  If `γ` is a dipath and a directed space `X` is covered by two opens `X₁` and `X₂`, then `γ` is n-covered for some `n`.
-/
lemma has_subpaths {X₁ X₂ : Set X} (hX : X₁ ∪ X₂ = Set.univ) (X₁_open : IsOpen X₁)
  (X₂_open : IsOpen X₂) (γ : Dipath x₀ x₁) :
    ∃ (n : ℕ), covered_partwise hX γ n := by
  have := has_interval_division hX X₁_open X₂_open γ
  rcases this with ⟨n, n_pos, hn⟩
  use n-1
  apply covered_partwise_of_covered_by_intervals
  simp
  intros i hi
  have h : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos n_pos
  have := hn i (by linarith)
  convert this <;> nth_rewrite 2 [←h] <;> simp
end covered_partwise
end Dipath
end
end Lean4_path_cover
/-! Source module: Lean4.split_dihomotopy -/
section Lean4_split_dihomotopy
/-
  This file contains the definitions of splitting a (dipath) dihomotopy both vertically and horizontally.
  Take a dihomotopy `F : f ~ g`, with `f g : D(I, X)`:
   *----- g -----*
   |             |
   |             |
   |             |
   |             |
   *----- f -----*
  Splitting vertically at `T : I` gives us:
    *----- g -----*
    |             |
    |             |
    *-- F.eval T -*
  and
    *-- F.eval T -*
    |             |
    |             |
    *----- f -----*
  Splitting horizontally at `T : I` gives us:
   *-- g₁ --*     *-- g₂ --*
   |        |     |        |
   |        | and |        |
   |        |     |        |
   |        |     |        |
   *-- f₁ --*     *-- f₂ --*
  Here f₁, f₂, g₁ and g₂ are obtained from f and g by splitting them at T : I.
  In the case that F is a dipath dihomotopy (it fixes endpoints), then splitting it vertically gives two dipath dihomotopies.
-/
open DirectedMap
open scoped unitInterval
namespace SplitDihomotopy
variable {X : dTopCat}
/--
For any `T: I`, we have the directed map `I → I` given by `t ↦ t * T`.
This is an interpolation from 0 to T
-/
abbrev DirectedFst (T : I) : D(I, I) := directed_interpolate_const (unitIAux.zero_le T)
@[simp]
lemma directedFst_apply (T t : I) : DirectedFst T t = ⟨_, unitInterval.mul_mem T.2 t.2⟩ := by
  apply Subtype.coe_inj.mp
  show (σ t : ℝ) * 0 + t * T = T * t
  ring
/--
For any `T : I` we have the directed map `I → I` given by `t ↦ (1 - t) * T + t`.
This is an interpolation from T to 1
-/
abbrev DirectedSnd (T : I) : D(I, I) := directed_interpolate_const (unitIAux.le_one T)
@[simp]
lemma directedSnd_apply (T t : I) : DirectedSnd T t = ⟨_, interp_left_mem_I T t⟩ := by
  apply Subtype.coe_inj.mp
  show (1 - t : ℝ) * T + t * 1 = (1 - T : ℝ) * t + T
  ring
/- Splitting a dipath-dihomotopy vertically -/
def FirstPartVerticallyDihomotopy {x y : X} {γ₁ γ₂ : Dipath x y} (F : Dipath.Dihomotopy γ₁ γ₂) (T : I) :
    Dipath.Dihomotopy γ₁ (F.eval T) where
  toDirectedMap := F.toDirectedMap.comp (DirectedMap.prod_map_mk' (DirectedFst T) (DirectedMap.id I))
  map_zero_left := fun x => by show F (DirectedFst T 0, x) = γ₁ x; simp
  map_one_left := fun x => by show F (DirectedFst T 1, x) = F (T, x); simp
  prop' := fun t z hz => F.prop' _ z hz
lemma fpv_apply {x y : X} {γ₁ γ₂ : Dipath x y} (F : Dipath.Dihomotopy γ₁ γ₂) (T s t : I) :
    FirstPartVerticallyDihomotopy F T (s, t) = F (T * s, t) := by
  show F (DirectedFst T s, t) = F (T * s, t)
  rw [directedFst_apply]
  rfl
/- Splitting a dipath-dihomotopy vertically -/
def SecondPartVerticallyDihomotopy {x y : X} {γ₁ γ₂ : Dipath x y} (F : Dipath.Dihomotopy γ₁ γ₂) (T : I) :
    Dipath.Dihomotopy (F.eval T) γ₂ where
  toDirectedMap := F.toDirectedMap.comp (DirectedMap.prod_map_mk' (DirectedSnd T) (DirectedMap.id I))
  map_zero_left := fun x => by show F (DirectedSnd T 0, x) = F (T, x); simp
  map_one_left := fun x => by show F (DirectedSnd T 1, x) = γ₂ x; simp
  prop' := fun t z hz => by
      show F (DirectedSnd T t, z) = F (T, z)
      have : F (T, z) = _ := (F.prop' T z hz)
      rw [this]
      exact (F.prop' _ z hz)
lemma spv_apply {x y : X} {γ₁ γ₂ : Dipath x y} (F : Dipath.Dihomotopy γ₁ γ₂) (T s t : I) :
    SecondPartVerticallyDihomotopy F T (s, t) = F (⟨_, interp_left_mem_I T s⟩, t) := by
  show F (DirectedSnd T s, t) = F (_, t)
  rw [directedSnd_apply]
/- Splitting a dihomotopy horizontally -/
def FirstPartHorizontallyDihomotopy {f g : D(I, X)} (F : Dihomotopy f g) (T : I) :
    Dihomotopy (SplitDipath.FirstPart (Dipath.of_directedMap f) T).toDirectedMap
               (SplitDipath.FirstPart (Dipath.of_directedMap g) T).toDirectedMap where
  toDirectedMap := F.toDirectedMap.comp (DirectedMap.prod_map_mk' (DirectedMap.id I) (DirectedFst T))
  map_zero_left := fun x => by
    show F (0, DirectedFst T x) = SplitDipath.FirstPart (Dipath.of_directedMap f) T x
    simp
    rfl
  map_one_left := fun x => by
    show F (1, DirectedFst T x) = SplitDipath.FirstPart (Dipath.of_directedMap g) T x
    simp
    rfl
lemma fph_apply {f g : D(I, X)} (F : Dihomotopy f g) (T s t : I) :
    FirstPartHorizontallyDihomotopy F T (s, t) = F (s, T * t) := by
  show F (s, DirectedFst T t) = F (s, _)
  rw [directedFst_apply]
  rfl
/- Splitting a dihomotopy horizontally -/
def SecondPartHorizontallyDihomotopy {f g : D(I, X)} (F : Dihomotopy f g) (T : I) :
    Dihomotopy (SplitDipath.SecondPart (Dipath.of_directedMap f) T).toDirectedMap
               (SplitDipath.SecondPart (Dipath.of_directedMap g) T).toDirectedMap where
  toDirectedMap := F.toDirectedMap.comp (DirectedMap.prod_map_mk' (DirectedMap.id I) (DirectedSnd T))
  map_zero_left := fun x => by
    show F (0, DirectedSnd T x) = SplitDipath.SecondPart (Dipath.of_directedMap f) T x
    simp
    rfl
  map_one_left := fun x => by
    show F (1, DirectedSnd T x) = SplitDipath.SecondPart (Dipath.of_directedMap g) T x
    simp
    rfl
lemma sph_apply {f g : D(I, X)} (F : Dihomotopy f g) (T s t : I) :
    SecondPartHorizontallyDihomotopy F T (s, t) = F (s, ⟨_, interp_left_mem_I T t⟩) := by
  show F (s, DirectedSnd T t) = F (s, _)
  rw [directedSnd_apply]
lemma fph_eval_0 {f g : D(I, X)} (F : Dihomotopy f g) (T : I) :
    (FirstPartHorizontallyDihomotopy F T).eval_at_right 0 = (F.eval_at_right 0).cast (by simp) (by simp) := by
  ext t
  show F (t, DirectedFst T 0) = F (t, 0)
  simp
lemma fph_eval_1 {f g : D(I, X)} (F : Dihomotopy f g) (T : I) :
    (FirstPartHorizontallyDihomotopy F T).eval_at_right 1 = (F.eval_at_right T).cast (by { simp; rfl }) (by { simp; rfl }) := by
  ext t
  show F (t, DirectedFst T 1) = F (t, T)
  simp
lemma sph_eval_0 {f g : D(I, X)} (F : Dihomotopy f g) (T : I) :
    (SecondPartHorizontallyDihomotopy F T).eval_at_right 0 = (F.eval_at_right T).cast (by { simp; rfl }) (by { simp; rfl }) := by
  ext t
  show F (t, DirectedSnd T 0) = F (t, T)
  simp
lemma sph_eval_1 {f g : D(I, X)} (F : Dihomotopy f g) (T : I) :
    (SecondPartHorizontallyDihomotopy F T).eval_at_right 1 = (F.eval_at_right 1).cast (by simp) (by simp) := by
  ext t
  show F (t, DirectedSnd T 1) = F (t, 1)
  simp
end SplitDihomotopy
end Lean4_split_dihomotopy
/-! Source module: Lean4.dihomotopy_cover -/
section Lean4_dihomotopy_cover
/-
  This file contains the definition of a (n, m)-covered (dipath) dihomotopy, covered by X₁ and X₂:
      It maps all subrectangles  [i/n, (i+1)/n] × [j/m, (j+1)/m] into either X₁ or X₂
  Conditions for being (n, m)-covered are given.
  Two paths are called (n, m)-dihomotopic if a (n, m)-covered path dihomotopy between them exists.
-/
open Set DirectedMap
open scoped unitInterval
noncomputable section
namespace DirectedMap
namespace Dihomotopy
variable {X : dTopCat} {f g : D(I, X)} {X₀ X₁ : Set X}
/--
  A dihomotopy of directed maps is covered if its image lies entirely in X₀ or in X₁.
-/
def covered (F : Dihomotopy f g) (_ : X₀ ∪ X₁ = univ) : Prop := range F ⊆ X₀ ∨ range F ⊆ X₁
/--
  A dihomotopy of directed maps is covered partwise n m if it can be covered by
  rectangles (n+1 vertically, m+1 horizontally) such that each rectangle is covered by either X₀ or X₁
-/
def coveredPartwise (_ : X₀ ∪ X₁ = univ) (F : Dihomotopy f g) (n m : ℕ) : Prop :=
  ∀ (i j : ℕ) (hi : i < n.succ) (hj : j < m.succ),
    F '' (UnitSubrectangle hi hj) ⊆ X₀ ∨ F '' (UnitSubrectangle hi hj) ⊆ X₁
/--
  A dihomotopy that can be covered partwise by `1 × 1` squares is covered.
-/
lemma covered_of_coveredPartwise {F : Dihomotopy f g} {hX : X₀ ∪ X₁ = univ} (hF : coveredPartwise hX F 0 0) :
    covered F hX := by
  unfold covered
  cases hF 0 0 zero_lt_one zero_lt_one
  case inl h =>
    left
    rintro x ⟨⟨t₀, t₁⟩, ht⟩
    rw [←ht]
    exact h ⟨(t₀, t₁), UnitSubrectangle.mem_unitSquare _, rfl⟩
  case inr h =>
    right
    rintro x ⟨⟨t₀, t₁⟩, ht⟩
    rw [←ht]
    exact h ⟨(t₀, t₁), UnitSubrectangle.mem_unitSquare _, rfl⟩
/--
If `F : f ∼ g` is a dihomotopy of directed maps, then the image of `f` restricted to `[i/(m+1), (i+1)/(m+1)]`
is contained in the image of `F` restricted to `[0, 1/(n+1)] × [i/(m+1), (i+1)/(m+1)]`.
-/
lemma left_path_image_interval_subset_of_dihomotopy_subset (F : Dihomotopy f g) (n : ℕ) {i m : ℕ} (hi : i < m.succ) :
    (Dipath.of_directedMap f).toPath.extend '' Icc (↑i / (↑m + 1)) ((↑i + 1) / (↑m + 1)) ⊆
      F ''  UnitSubrectangle (Nat.succ_pos n) hi := by
  rintro x ⟨t, ⟨ht, rfl⟩⟩
  have tI : t ∈ I := UnitIntervalSub.mem_I_of_mem_interval_coed hi ht
  rw [Path.extend_extends (Dipath.of_directedMap f).toPath tI]
  use (0, ⟨t, tI⟩)
  constructor
  · apply UnitSubrectangle.mem_unitSubrectangle
    constructor
    · norm_num
    · apply div_nonneg
      · norm_num
      · exact Nat.cast_nonneg _
    · convert ht <;> exact Nat.cast_succ _
  · simp; rfl
/--
If `F : f ∼ g` is a dihomotopy of directed maps, and `F` is `n × m`-covered, then `f` is `m`-covered.
-/
lemma path_covered_partiwse_of_dihomotopy_coveredPartwise_left {F : Dihomotopy f g} {hX : X₀ ∪ X₁ = univ}
  {n m : ℕ} (hF : coveredPartwise hX F n m) :
    Dipath.covered_partwise hX (Dipath.of_directedMap f) m := by
  apply Dipath.covered_partwise.covered_partwise_of_covered_by_intervals
  intros i hi
  cases hF 0 i (Nat.succ_pos n) hi
  case inl h =>
    left
    exact subset_trans (left_path_image_interval_subset_of_dihomotopy_subset F n hi) h
  case inr h =>
    right
    exact subset_trans (left_path_image_interval_subset_of_dihomotopy_subset F n hi) h
/--
If `F : f ∼ g` is a dihomotopy of directed maps, then the image of `g` restricted to `[i/(m+1), (i+1)/(m+1)]`
is contained in the image of `F` restricted to `[n/(n+1), 1] × [i/(m+1), (i+1)/(m+1)]`.
-/
lemma right_path_image_interval_subset_of_dihomotopy_subset (F : Dihomotopy f g) (n : ℕ) {i m : ℕ} (hi : i < m.succ) :
    (Dipath.of_directedMap g).toPath.extend '' Icc (↑i / (↑m + 1)) ((↑i + 1) / (↑m + 1)) ⊆
      F ''  UnitSubrectangle (Nat.lt_succ_self n) hi := by
  rintro x ⟨t, ⟨ht, rfl⟩⟩
  have tI : t ∈ I := UnitIntervalSub.mem_I_of_mem_interval_coed hi ht
  rw [Path.extend_extends (Dipath.of_directedMap g).toPath tI]
  use (1, ⟨t, tI⟩)
  constructor
  · apply UnitSubrectangle.mem_unitSubrectangle
    · constructor
      · exact (div_le_one (show (n.succ : ℝ) > 0 by
          exact Nat.cast_pos.mpr (Nat.succ_pos n))).mpr (Nat.cast_le.mpr (Nat.le_succ n))
      · rw [div_self]
        exact Nat.cast_ne_zero.mpr (ne_of_gt (Nat.succ_pos n))
    · convert ht <;> exact Nat.cast_succ _
  · simp; rfl
/--
If `F : f ∼ g` is a dihomotopy of directed maps, and `F` is `n × m`-covered, then `g` is `m`-covered.
-/
lemma path_covered_partiwse_of_dihomotopy_coveredPartwise_right {F : Dihomotopy f g}
  {hX : X₀ ∪ X₁ = univ} {n m : ℕ} (hF : coveredPartwise hX F n m) :
    Dipath.covered_partwise hX (Dipath.of_directedMap g) m := by
  apply Dipath.covered_partwise.covered_partwise_of_covered_by_intervals
  intros i hi
  cases hF n i (Nat.lt_succ_self n) hi
  case inl h =>
    left
    exact subset_trans (right_path_image_interval_subset_of_dihomotopy_subset F n hi) h
  case inr h =>
    right
    exact subset_trans (right_path_image_interval_subset_of_dihomotopy_subset F n hi) h
/--
If `F : f ∼ g` is a dihomotopy of directed maps, there exist `n m : ℕ` such that `F` is `n × m`-covered.
-/
lemma coveredPartwise_exists (F : Dihomotopy f g) (hX : X₀ ∪ X₁ = univ) (X₀_open : IsOpen X₀) (X₁_open : IsOpen X₁) :
    ∃ (n m : ℕ), coveredPartwise hX F n m := by
  set c : ℕ → Set (I × I) := fun i => if i = 0 then F ⁻¹' X₀ else F ⁻¹'  X₁ with c_def
  have h₁ : ∀ i, IsOpen (c i) := by
    intro i
    by_cases i = 0
    case pos  h =>
      simp [c_def, h]
      exact F.continuous_toFun.isOpen_preimage X₀ X₀_open
    case neg h =>
      simp [c_def, h]
      exact F.continuous_toFun.isOpen_preimage X₁ X₁_open
  have h₂ : UnitSquare ⊆ (⋃ (i : ℕ), c i) := by
    intro x _
    rw [Set.mem_iUnion]
    have hx : F x ∈ X₀ ∪ X₁ := hX.symm ▸ (Set.mem_univ $ F x)
    rcases hx with hx | hx
    · exact ⟨0, by simpa [c_def] using hx⟩
    · exact ⟨1, by simpa [c_def] using hx⟩
  rcases (lebesgue_number_lemma_unit_square h₁ h₂) with ⟨n, hn⟩
  use n
  use n
  intros i j hi hj
  cases (hn i j hi hj)
  case h.intro ι hι =>
    rw [c_def] at hι
    simp at hι
    by_cases ι = 0
    case pos h => left; simp [h] at hι; exact Set.image_subset_iff.mpr hι
    case neg h => right; simp [h] at hι; exact Set.image_subset_iff.mpr hι
/--
  The image of a dihomotopy F of the subrectangles `[0, 1/(n+2)] × [j/(m+1), (j+1)/(m+1)]`
  contains the image of the first part of F, split at `1/(n+2)`, of `[0, 1] × [j/(m+1), (j+1)/(m+1)]`.
-/
lemma fpv_subrectangle {x y : X} {γ₁ γ₂ : Dipath x y} {F : Dipath.Dihomotopy γ₁ γ₂} {n m j : ℕ} (hj : j < m.succ) :
    (SplitDihomotopy.FirstPartVerticallyDihomotopy F (Fraction.ofPos (Nat.succ_pos n.succ))).toDihomotopy ''
    (UnitSubrectangle zero_lt_one hj) ⊆ F '' (UnitSubrectangle (Nat.zero_lt_succ n.succ) hj) := by
  rintro z ⟨⟨t₀, t₁⟩, ⟨tI, ht⟩⟩
  have : ((SplitDihomotopy.FirstPartVerticallyDihomotopy F _).toDihomotopy) (t₀, t₁) =
    (SplitDihomotopy.FirstPartVerticallyDihomotopy F (Fraction.ofPos (Nat.succ_pos n.succ))) (t₀, t₁) := rfl
  rw [this, SplitDihomotopy.fpv_apply] at ht
  show ∃ a, a ∈ UnitSubrectangle _ hj ∧ F a = z
  refine' ⟨_, _, ht⟩
  constructor
  constructor
  · rw [Fraction.eq_zero]
    unit_interval
  · exact unitInterval.mul_le_left
  · exact tI.2
/--
  If F is `(n+1) × m`-covered, then the first part of F, split at `T = 1/(n+2)` is `0 x m`-covered.
-/
lemma coveredPartwise_first_vpart {x y : X} {γ₁ γ₂ : Dipath x y} {F : Dipath.Dihomotopy γ₁ γ₂}
  {hX : X₀ ∪ X₁ = univ} {n m : ℕ} (hF : coveredPartwise hX F.toDihomotopy n.succ m) :
    coveredPartwise hX (SplitDihomotopy.FirstPartVerticallyDihomotopy F
      (Fraction.ofPos (Nat.succ_pos n.succ))).toDihomotopy 0 m := by
  unfold coveredPartwise at hF
  unfold coveredPartwise
  intros i j hi hj
  obtain ⟨rfl⟩ : i = 0 := by linarith
  cases (hF 0 j (Nat.succ_pos n.succ) hj)
  case inl h => left; exact subset_trans (fpv_subrectangle _) h
  case inr h => right; exact subset_trans (fpv_subrectangle _) h
/--
  If `i/(n+1) ≤ t`, then `(i+1)/(n+2) ≤ (σ q) * t + q`, where `q = 1/(n+2)`
-/
lemma spv_aux₁_coed {t : ℝ} {n i : ℕ} (_ : i < n.succ) (ht : (i : ℝ)/(n.succ : ℝ) ≤ t) :
    (i+1 : ℝ) / (n+2 : ℝ) ≤ (1 - 1/(n+1+1)) * t + (1/(n+1+1)) := by
  have h₀ : 0 ≤ (i : ℝ)/(n.succ : ℝ) := by
    apply div_nonneg
    exact Nat.cast_nonneg i
    exact Nat.cast_nonneg n.succ
  have h₁ : 0 ≤ t := le_trans h₀ ht
  have h₂ : (n.succ : ℝ) > 0 := Nat.cast_pos.mpr (Nat.succ_pos n)
  have h₃ : 0 ≤ (n : ℝ) + 1 := by
    apply le_of_lt
    rw [Nat.cast_succ _] at h₂
    exact h₂
  rw [FractionEqualities.one_sub_inverse_of_add_one (by positivity), mul_comm, mul_div, div_add_div_same]
  apply div_le_div₀
  · linarith [mul_nonneg h₁ h₃]
  · apply add_le_add_left
    calc (i : ℝ)
      _ = ↑i * 1                      := by rw [mul_one]
      _ = ↑i * ((↑n.succ)/(↑n.succ))  := by rw [div_self (ne_of_gt h₂)]
      _ = ↑i/(↑n.succ) * (↑n.succ)    := by ring
      _ ≤ t * (↑n.succ)               := mul_le_mul_of_nonneg_right ht (le_of_lt h₂)
      _ = t * (↑n+1)                  := by rw [Nat.cast_succ]
  · positivity
  · exact le_of_eq (by ring)
/--
  If `i/(n+1) ≤ t`, then `(i+1)/(n+2) ≤ (σ q) * t + q`, where `q = 1/(n+2)`
-/
lemma spv_aux₁ {t : I} {n i : ℕ} (hi : i < n.succ) (ht : Fraction (Nat.succ_pos n) (le_of_lt hi) ≤ t) :
  Fraction (Nat.succ_pos n.succ) (le_of_lt (Nat.succ_lt_succ hi)) ≤
    (⟨_, interp_left_mem_I (Fraction (Nat.succ_pos n.succ) (Nat.succ_le_succ (Nat.zero_le n.succ))) t⟩ : I) := by
  apply Subtype.coe_le_coe.mp
  convert spv_aux₁_coed hi ht using 1
  rw [Fraction.Fraction_coe]
  congr 1 <;> simp; ring
  simp
/--
  If `t ≤ (i+1)/(n+1)`, then `(σ q) * t + q ≤ (i+2)/(n+2)`, where `q = 1/(n+2)`
-/
lemma spv_aux₂_coed {t : ℝ} {n i : ℕ} (_ : i < n.succ) (ht₀ : 0 ≤ t) (ht : t ≤ (i.succ : ℝ)/(n.succ : ℝ)) :
    (1 - 1/(n+1+1 : ℝ)) * t + (1/(n+1+1 : ℝ)) ≤ (i+2 : ℝ) / (n+2 : ℝ) := by
  have h₀ : (n.succ : ℝ) > 0 := Nat.cast_pos.mpr (Nat.succ_pos n)
  have h₁ : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
  have h₂ : (i : ℝ) ≥ 0 := Nat.cast_nonneg i
  rw [FractionEqualities.one_sub_inverse_of_add_one (by positivity), mul_comm, mul_div, div_add_div_same]
  apply div_le_div₀ <;> try linarith
  · rw [←one_add_one_eq_two, ←add_assoc]
    apply add_le_add_left
    calc t * (n + 1 : ℝ)
      _ = t * (↑n.succ)                   := by rw [Nat.cast_succ]
      _ ≤ (↑i.succ)/(↑n.succ) * (↑n.succ) := mul_le_mul_of_nonneg_right ht (le_of_lt h₀)
      _ = (↑n.succ)/(↑n.succ) * (↑i.succ) := by ring
      _ = 1 * (↑i.succ)                   := by rw [div_self (ne_of_gt h₀)]
      _ = (↑i.succ)                       := one_mul _
      _ = (↑i + 1)                        := by rw [Nat.cast_succ]
/--
  If `t ≤ (i+1)/(n+1)`, then `(σ q) * t + q ≤ (i+2)/(n+2)`, where `q = 1/(n+2)`
-/
lemma spv_aux₂ {t : I} {n i : ℕ} (hi : i < n.succ) (ht : t ≤ Fraction (Nat.succ_pos n) (Nat.succ_le_of_lt hi)) :
    (⟨_, interp_left_mem_I (Fraction (Nat.succ_pos n.succ) (Nat.succ_le_succ (Nat.zero_le n.succ))) t⟩ : I) ≤
      Fraction (Nat.succ_pos n.succ) (Nat.succ_le_of_lt (Nat.succ_lt_succ hi)) := by
  apply Subtype.coe_le_coe.mp
  convert spv_aux₂_coed hi t.2.1 ht using 1
  simp
  rw [Fraction.Fraction_coe]
  congr 1 <;> rw [Nat.cast_succ, Nat.cast_succ] <;> linarith
/--
  The image of a dihomotopy F of the subrectangle `[(i+1)/(n+2), (i+2)/(n+2)] × [j/(m+1), (j+1)/(m+1)]`
  contains the image of the second part of F, split at `1/(n+2)`, of `[i/(n+1), (i+1)/(n+1)] × [j/(m+1), (j+1)/(m+1)]`.
-/
lemma spv_subrectangle {x y : X} {γ₁ γ₂ : Dipath x y} {F : Dipath.Dihomotopy γ₁ γ₂} {n m i j : ℕ}
  (hi : i < n.succ) (hj : j < m.succ) :
    (SplitDihomotopy.SecondPartVerticallyDihomotopy F (Fraction.ofPos (Nat.succ_pos n.succ))).toDihomotopy ''
    (UnitSubrectangle hi hj) ⊆ F '' (UnitSubrectangle (Nat.succ_lt_succ hi) hj) := by
  rintro z ⟨⟨t₀, t₁⟩, ⟨tI, ht⟩⟩
  have : ((SplitDihomotopy.SecondPartVerticallyDihomotopy F _).toDihomotopy) (t₀, t₁) =
          (SplitDihomotopy.SecondPartVerticallyDihomotopy F (Fraction.ofPos (Nat.succ_pos n.succ))) (t₀, t₁) := rfl
  rw [this, SplitDihomotopy.spv_apply] at ht
  show ∃ a, a ∈ UnitSubrectangle _ hj ∧ F a = z
  refine' ⟨_, _, ht⟩
  constructor
  constructor
  · exact spv_aux₁ hi tI.1.1
  · exact spv_aux₂ hi tI.1.2
  · exact tI.2
/--
  If F is  `(n + 1) × m`-covered, then the second part of F, split at `T = 1/(n+1)` is `n × m`-covered.
-/
lemma coveredPartwise_second_vpart {x y : X} {γ₁ γ₂ : Dipath x y} {F : Dipath.Dihomotopy γ₁ γ₂}
  {hX : X₀ ∪ X₁ = univ} {n m : ℕ} (hF : coveredPartwise hX F.toDihomotopy n.succ m) :
    coveredPartwise hX (SplitDihomotopy.SecondPartVerticallyDihomotopy F
      (Fraction.ofPos (Nat.succ_pos n.succ))).toDihomotopy n m := by
  unfold coveredPartwise at hF
  unfold coveredPartwise
  intros i j hi hj
  cases (hF i.succ j (Nat.succ_lt_succ hi) hj)
  case inl h => left; exact subset_trans (spv_subrectangle _ _) h
  case inr h => right; exact subset_trans (spv_subrectangle _ _) h
/--
  The image of a dihomotopy F of the rectangle `[i/(n+1), (i+1)/(n+1)] × [0, 1/(m+2)]`
  contains the image of the first part of F, split at `1/(m+2)`, of `[i/(n+1), (i+1)/(n+1)] × [0, 1]`.
-/
lemma fph_subrectangle {f g : D(I, X)} {F : Dihomotopy f g} {n m i : ℕ} (hi : i < n.succ) :
    (SplitDihomotopy.FirstPartHorizontallyDihomotopy F (Fraction.ofPos (Nat.succ_pos m.succ))) ''
      (UnitSubrectangle hi zero_lt_one) ⊆ F '' (UnitSubrectangle hi (Nat.succ_pos m.succ)) := by
  rintro z ⟨⟨t₀, t₁⟩, ⟨tI, ht⟩⟩
  rw [SplitDihomotopy.fph_apply] at ht
  show ∃ a, a ∈ UnitSubrectangle hi _ ∧ F a = z
  refine' ⟨_, _, ht⟩
  constructor
  · exact tI.1
  · constructor
    · rw [Fraction.eq_zero]
      unit_interval
    · exact unitInterval.mul_le_left
/--
  If `F` is `n × (m+1)`-covered, then the first part of `F`, split at `T = 1/(m+2)`, is `n × 0`-covered.
-/
lemma coveredPartwise_first_hpart {f g : D(I, X)} {F : Dihomotopy f g} {hX : X₀ ∪ X₁ = univ} {n m : ℕ}
  (hF : coveredPartwise hX F n m.succ) :
    coveredPartwise hX (SplitDihomotopy.FirstPartHorizontallyDihomotopy F
      (Fraction.ofPos (Nat.succ_pos m.succ))) n 0 := by
  unfold coveredPartwise at hF
  unfold coveredPartwise
  intros i j hi hj
  obtain ⟨rfl⟩ : j = 0 := by linarith
  cases (hF i 0 hi (Nat.succ_pos m.succ))
  case inl h => left; exact subset_trans (fph_subrectangle _) h
  case inr h => right; exact subset_trans (fph_subrectangle _) h
/--
  The image of a dihomotopy F of the rectangle `[i/(n+1), (i+1)/(n+1)] × [(j+1)/(m+2), (j+2)/(m+2)]`
  contains the image of the second part of F, split at `1/(m+2)`, of
  `[i/(n+1), (i+1)/(n+1)] × [j/(m+1), (j+1)/(m+1)]`.
-/
lemma sph_subrectangle {f g : D(I, X)} {F : Dihomotopy f g} {n m i j : ℕ} (hi : i < n.succ) (hj : j < m.succ) :
    (SplitDihomotopy.SecondPartHorizontallyDihomotopy F (Fraction.ofPos (Nat.succ_pos m.succ))) ''
      (UnitSubrectangle hi hj) ⊆ F '' (UnitSubrectangle hi (Nat.succ_lt_succ hj)) := by
  rintro z ⟨⟨t₀, t₁⟩, ⟨tI, ht⟩⟩
  rw [SplitDihomotopy.sph_apply] at ht
  show ∃ a, a ∈ UnitSubrectangle hi _ ∧ F a = z
  refine' ⟨_, _, ht⟩
  constructor
  · exact tI.1
  · constructor
    · exact spv_aux₁ hj tI.2.1
    · exact spv_aux₂ hj tI.2.2
/--
  If `F` is `n × (m+1)`-covered, then the second part of `F`, split at at `T = 1/(n+1)` is `n × m`-covered.
-/
lemma coveredPartwise_second_hpart {f g : D(I, X)} {F : Dihomotopy f g} {hX : X₀ ∪ X₁ = univ} {n m : ℕ}
  (hF : coveredPartwise hX F n m.succ) :
    coveredPartwise hX (SplitDihomotopy.SecondPartHorizontallyDihomotopy F
      (Fraction.ofPos (Nat.succ_pos m.succ))) n m := by
  unfold coveredPartwise at hF
  unfold coveredPartwise
  intros i j hi hj
  cases (hF i j.succ hi (Nat.succ_lt_succ hj))
  case inl h => left; exact subset_trans (sph_subrectangle _ _) h
  case inr h => right; exact subset_trans (sph_subrectangle _ _) h
end Dihomotopy
end DirectedMap
namespace Dipath
namespace Dihomotopy
variable {X : dTopCat} {X₀ X₁ : Set X} {x y : X} {γ₁ γ₂ : Dipath x y}
lemma range_left_subset (F : Dihomotopy γ₁ γ₂) : range γ₁ ⊆ range F :=
  fun _ ⟨t, ht⟩ => ⟨(0 , t), ht ▸ F.map_zero_left t⟩
lemma range_right_subset (F : Dihomotopy γ₁ γ₂) : range γ₂ ⊆ range F :=
  fun _ ⟨t, ht⟩ => ⟨(1 , t), ht ▸ F.map_one_left t⟩
/--
  A dihomotopy of directed paths is covered if its image lies entirely in X₀ or in X₁.
-/
def covered (_ : X₀ ∪ X₁ = univ) (F : Dihomotopy γ₁ γ₂) : Prop := range F ⊆ X₀ ∨ range F ⊆ X₁
/--
If `F : γ₁ ∼ γ₂` is a dihomotopy of directed paths, and `F` is covered, then `γ₁` is covered.
-/
lemma covered_left_of_covered {F : Dihomotopy γ₁ γ₂} {hX : X₀ ∪ X₁ = univ} (hF : covered hX F) :
    Dipath.covered hX γ₁ :=
  Or.elim hF
    (fun hF => Or.inl (subset_trans (range_left_subset F) hF))
    (fun hF => Or.inr (subset_trans (range_left_subset F) hF))
/--
If `F : γ₁ ∼ γ₂` is a dihomotopy of directed paths, and `F` is covered, then `γ₂` is covered.
-/
lemma covered_right_of_covered {F : Dihomotopy γ₁ γ₂} {hX : X₀ ∪ X₁ = univ} (hF : covered hX F) :
    Dipath.covered hX γ₂ :=
  Or.elim hF
    (fun hF => Or.inl (subset_trans (range_right_subset F) hF))
    (fun hF => Or.inr (subset_trans (range_right_subset F) hF))
/--
  Two paths are `m × n`-dihomotopic if there is a dihomotopy between them that can be covered by `m × n` rectangles.
-/
def dihomotopicCovered (hX : X₀ ∪ X₁ = univ) (γ₁ γ₂ : Dipath x y) (n m : ℕ) : Prop :=
  ∃ (F : Dihomotopy γ₁ γ₂), DirectedMap.Dihomotopy.coveredPartwise hX F.toDihomotopy n m
/--
  If `γ₁` and `γ₂` are two paths connected by a path-dihomotopy `F` that is covered by `m × (n + 1)` rectangles,
  then `γ₁` and `F.eval (1/(n+2))` are `m × 0`-dihomotopic and `F.eval (1/(n+2))` and `γ₂` are `m × n`-dihomotopic.
-/
lemma dihomotopicCovered_split {F : Dihomotopy γ₁ γ₂} (hX : X₀ ∪ X₁ = univ) {n m : ℕ}
  (hF : DirectedMap.Dihomotopy.coveredPartwise hX F.toDihomotopy n.succ m) :
    dihomotopicCovered hX γ₁ (F.eval (Fraction.ofPos (Nat.succ_pos n.succ))) 0 m ∧
    dihomotopicCovered hX (F.eval (Fraction.ofPos (Nat.succ_pos n.succ))) γ₂ n m := by
  constructor
  · exact ⟨_, DirectedMap.Dihomotopy.coveredPartwise_first_vpart hF⟩
  · exact ⟨_, DirectedMap.Dihomotopy.coveredPartwise_second_vpart hF⟩
/--
  If `γ₁` and `γ₂` are two directed paths paths such that there is some dihomotopy between them,
  then there are `n m : ℕ` such that `γ₁` and `γ₂` are `n × m`-dihomotopicCovered.
-/
lemma dihomotopicCovered_exists_of_preDihomotopic (hX : X₀ ∪ X₁ = univ) (h : γ₁.PreDihomotopic γ₂)
  (X₀_open : IsOpen X₀) (X₁_open : IsOpen X₁) :
    ∃ (n m : ℕ), dihomotopicCovered hX γ₁ γ₂ n m := by
  rcases (DirectedMap.Dihomotopy.coveredPartwise_exists h.some.toDihomotopy hX X₀_open X₁_open) with ⟨n, m, hnm⟩
  exact ⟨n, m, h.some, hnm⟩
end Dihomotopy
end Dipath
end
end Lean4_dihomotopy_cover
/-! Source module: Lean4.pushout_alternative -/
section Lean4_pushout_alternative
/-
  This file contains an alternative way for proving a commutative square in a category is a pushout.
-/
universe u
open CategoryTheory
namespace PushoutAlternative
variable {X X₁ X₂ X₀ : Cat.{u, u}} {i₁: X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ X} {j₂: X₂ ⟶ X}
lemma isPushout_alternative (h_comm : i₁ ≫ j₁ = i₂ ≫ j₂)
  (h_uniq : ∀ (C : Cat.{u, u}) (F₁ : X₁ ⟶ C) (F₂ : X₂ ⟶ C) (_ : i₁ ≫ F₁ = i₂ ≫ F₂),
      ∃! (F : X ⟶ C), j₁ ≫ F = F₁ ∧ j₂ ≫ F = F₂) :
    IsPushout i₁ i₂ j₁ j₂ := by
  let w : CommSq i₁ i₂ j₁ j₂ := { w := h_comm }
  have : ∀ (s : Limits.Cocone (Limits.span i₁ i₂)),
    i₁ ≫ Limits.PushoutCocone.inl s = i₂ ≫ Limits.PushoutCocone.inr s := Limits.PushoutCocone.condition
  let desc : ∀ (s : Limits.PushoutCocone i₁ i₂), X ⟶ s.pt := fun s => Classical.choose (h_uniq s.pt _ _ (this s))
  have fac_left : ∀ (s : Limits.PushoutCocone i₁ i₂), j₁ ≫ desc s = s.inl := fun s => (Classical.choose_spec (h_uniq s.pt _ _ (this s))).1.1
  have fac_right : ∀ (s : Limits.PushoutCocone i₁ i₂), j₂ ≫ desc s = s.inr := fun s => (Classical.choose_spec (h_uniq s.pt _ _ (this s))).1.2
  have uniq : ∀ (s : Limits.PushoutCocone i₁ i₂) (m : X ⟶ s.pt) (_ : ∀ j : Limits.WalkingSpan, w.cocone.ι.app j ≫ m = s.ι.app j), m = desc s := by
    rintro s m h
    apply (Classical.choose_spec (h_uniq s.pt _ _ (this s))).right
    exact ⟨h Limits.WalkingCospan.left, h Limits.WalkingCospan.right⟩
  exact IsPushout.of_isColimit' w (Limits.PushoutCocone.isColimitAux _ desc fac_left fac_right uniq)
end PushoutAlternative
end Lean4_pushout_alternative
/-! Source module: Lean4.dihomotopy_flip -/
section Lean4_dihomotopy_flip
/-
  If we have a dihomotopy `F` from `f : D(I, X)` to `g : D(I, X)`:
    C----- g -----D
    |             |
    |             |
    |             |
    |             |
    A----- f -----B
  Then we can flip it diagonally to obtain a new homotopy:
    B--- F.eval_at_right 1 -----D
    |                           |
    f                           g
    |                           |
    |                           |
    A----F.eval_at_right 0 -----C
  We then use that to compose two homotopies F
    D----- q₀ -----E
    |              |
    |              |
    |              |
    |              |
    A----- p₀ -----B
  and G
    E----- q₁ -----F
    |              |
    |              |
    |              |
    |              |
    B----- p₁ -----C
  that agree on the common side B ----- E to
    D----- q₀.trans q₁ -----F
    |                       |
    |                       |
    |                       |
    |                       |
    A----- p₀.trans p₁ -----C
  This is a variation of dipath.dihomotopy.hcomp of dihomotopies that are not necessarily dipath dihomotopies.
-/
universe u v
open DirectedSpace DirectedUnitInterval unitIAux DirectedMap
open scoped unitInterval
noncomputable section
namespace DirectedMap
namespace Dihomotopy
variable {X : dTopCat} {f g : D(I, X)}
def flip (F : Dihomotopy f g) : Dihomotopy (F.eval_at_right 0).toDirectedMap (F.eval_at_right 1).toDirectedMap :=
{
  toContinuousMap := ⟨fun t => F (t.2, t.1),
    F.continuous_toFun.comp (continuous_snd.prodMk continuous_fst)⟩
  directed_toFun := fun ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ γ ⟨h₁, h₂⟩ => by
      let γ' : Dipath (y₀, x₀) (y₁, x₁) := {
        toPath := {
          toContinuousMap := ⟨fun t => ((γ t).2, (γ t).1),
            (continuous_snd.prodMk continuous_fst).comp γ.continuous⟩
          source' := by simp
          target' := by simp
        }
        dipath_toPath := ⟨h₂, h₁⟩
      }
      exact F.directed_toFun γ'.toPath γ'.dipath_toPath
  map_zero_left := fun x => rfl
  map_one_left := fun x => rfl
}
lemma flip_apply (F : Dihomotopy f g) (t₀ t₁ : I) :
  F.flip (t₀, t₁) = F (t₁, t₀) := rfl
variable {x₀ x₁ x₂ y₀ y₁ y₂ : X}
variable {p₀ : Dipath x₀ x₁} {p₁ : Dipath x₁ x₂} {q₀ : Dipath y₀ y₁} {q₁ : Dipath y₁ y₂}
/--
Suppose the following are given:
* `p₀ : dipath x₀ x₁`
* `p₁ : dipath x₁ x₂`
* `q₀ : dipath y₀ y₁`
* `q₁ : dipath y₁ y₂`
* `F : dihomotopy p₀.toDirectedMap q₀.toDirectedMap`
* `G : dihomotopy p₁.toDirectedMap p₁.toDirectedMap`
* `h : F.eval_at_right 1 = G.eval_at_right 0`
Then we can compose these horizontally to obtain:
  `dihomotopy (p₀.trans p₁).toDirectedMap (q₀.trans q₁).toDirectedMap`
-/
def hcomp' (F : Dihomotopy p₀.toDirectedMap q₀.toDirectedMap) (G : Dihomotopy p₁.toDirectedMap q₁.toDirectedMap)
  (h : (F.eval_at_right 1).toDirectedMap = (G.eval_at_right 0).toDirectedMap) :
    Dihomotopy (p₀.trans p₁).toDirectedMap (q₀.trans q₁).toDirectedMap :=
  ((F.flip.cast rfl h).trans G.flip).flip.cast
    (by
      ext t
      show ((F.flip.cast rfl h).trans G.flip) (t, 0) = (p₀.trans p₁) t
      rw [trans_apply, Dipath.trans_apply]
      split_ifs
      · rw [cast_apply, flip_apply]
        exact F.map_zero_left _
      · rw [flip_apply]
        exact G.map_zero_left _
    )
    (by
      ext t
      show ((F.flip.cast rfl h).trans G.flip) (t, 1) = (q₀.trans q₁) t
      rw [trans_apply, Dipath.trans_apply]
      split_ifs
      · rw [cast_apply, flip_apply]
        exact F.map_one_left _
      · rw [flip_apply]
        exact G.map_one_left _
    )
lemma hcomp'_apply (F : Dihomotopy p₀.toDirectedMap q₀.toDirectedMap) (G : Dihomotopy p₁.toDirectedMap q₁.toDirectedMap)
  (h : (F.eval_at_right 1).toDirectedMap = (G.eval_at_right 0).toDirectedMap) (t₁ t₂ : I) :
    (hcomp' F G h) (t₁, t₂) =
    if h : (t₂ : ℝ) ≤ 1/2 then
      F.eval_at_left t₁ ⟨2 * t₂, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨t₂.2.1, h⟩⟩
    else
      G.eval_at_left t₁ ⟨2 * t₂ - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t₂.2.2⟩⟩ := by
  unfold hcomp'
  rw [cast_apply, flip_apply, trans_apply]
  split_ifs
  · rw [cast_apply, flip_apply]
    rfl
  · rw [flip_apply]
    rfl
lemma hcomp'_apply_zero_right (F : Dihomotopy p₀.toDirectedMap q₀.toDirectedMap) (G : Dihomotopy p₁.toDirectedMap q₁.toDirectedMap)
  (h : (F.eval_at_right 1).toDirectedMap = (G.eval_at_right 0).toDirectedMap) (x : I) :
    (hcomp' F G h) (x, 0) = F (x, 0) := by
  rw [hcomp'_apply]
  split_ifs with h
  · show F (x, _) = F (x, 0)
    apply congr_arg
    ext
    rfl
    simp
  · exfalso
    apply h
    show (0 : ℝ) ≤ 1/2
    linarith
lemma hcomp'_apply_one_right (F : Dihomotopy p₀.toDirectedMap q₀.toDirectedMap) (G : Dihomotopy p₁.toDirectedMap q₁.toDirectedMap)
  (h : (F.eval_at_right 1).toDirectedMap = (G.eval_at_right 0).toDirectedMap) (x : I) :
    (hcomp' F G h) (x, 1) = G (x, 1) := by
  rw [hcomp'_apply]
  split_ifs with h
  · exfalso
    have : ¬ ((1 : ℝ) ≤ 1/2) := by linarith
    apply this
    exact h
  · show G (x, _) = G (x, 1)
    apply congr_arg
    ext
    rfl
    simp
    norm_num
lemma hcomp'_range (F : Dihomotopy p₀.toDirectedMap q₀.toDirectedMap) (G : Dihomotopy p₁.toDirectedMap q₁.toDirectedMap)
  (h : (F.eval_at_right 1).toDirectedMap = (G.eval_at_right 0).toDirectedMap) :
    Set.range (hcomp' F G h) ⊆ Set.range F ∪ Set.range G := fun z ⟨⟨t₁, t₂⟩, ht⟩ =>  by
  rw [hcomp'_apply] at ht
  split_ifs at ht with h
  · left
    constructor
    exact ht
  · right
    constructor
    exact ht
end Dihomotopy
end DirectedMap
end
end Lean4_dihomotopy_flip
/-! Source module: Lean4.dihomotopy_to_path_dihomotopy -/
section Lean4_dihomotopy_to_path_dihomotopy
/-
  This file contains the construction of the following statement:
  Let a dihomotopy `F : f ~ g`, with `f g : D(I, X)` be  given:
   C----- g -----D
   |             |
   |             |
   |             |
   |             |
   A----- f -----B
  Then there is a path-dihomotopy between the paths
    A --refl A--> A --f--> B --F.eval_at_right 1--> D
  and
    A --F.eval_at_right 0--> C --g--> D --refl D--> D
-/
universe u
open DirectedMap
open scoped unitInterval
noncomputable section
namespace DirectedMap
namespace Dihomotopy
variable {X : dTopCat} {x y : X} (γ : Dipath x y)
def MinDirected : D(I × I, I) where
  toFun := fun t => min t.1 t.2
  continuous_toFun := Continuous.subtype_mk
    (continuous_min.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)))
    (fun t => ⟨le_min t.1.2.1 t.2.2.1,
      le_trans (min_le_left _ _) t.1.2.2⟩)
  directed_toFun := fun t₀ t₁ γ ⟨h₁, h₂⟩ a b hab => le_min (min_le_of_left_le (h₁ hab)) (min_le_of_right_le (h₂ hab))
def MaxDirected : D(I × I, I) where
  toFun := fun t => max t.1 t.2
  continuous_toFun := Continuous.subtype_mk
    (continuous_max.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)))
    (fun t => ⟨le_trans t.1.2.1 (le_max_left _ _),
      max_le t.1.2.2 t.2.2.2⟩)
  directed_toFun := fun t₀ t₁ γ ⟨h₁, h₂⟩ a b hab => max_le (le_max_of_le_left (h₁ hab)) (le_max_of_le_right (h₂ hab))
def SourceToPath : Dihomotopy (Dipath.refl x).toDirectedMap γ.toDirectedMap where
  toDirectedMap := γ.toDirectedMap.comp MinDirected
  map_zero_left := fun t => by
    show γ (min 0 t) = _
    have : min 0 t = 0 := min_eq_left t.2.1
    rw [this, γ.source]
    rfl
  map_one_left := fun t => by
    show γ (min 1 t) = _
    have : min 1 t = t := min_eq_right t.2.2
    rw [this]
    rfl
lemma sourceToPath_apply (s t : I) : SourceToPath γ (s, t) = γ (min s t) := rfl
lemma sourceToPath_range : Set.range (SourceToPath γ) = Set.range γ := by
  ext z
  constructor
  · intro ⟨t, ht⟩
    use min t.1 t.2
    rw [←ht]
    exact (sourceToPath_apply γ t.1 t.2).symm
  · intro ⟨t, ht⟩
    use (t, t)
    rw [←ht, sourceToPath_apply]
    exact congr_arg γ (min_self t)
def PathToTarget : Dihomotopy γ.toDirectedMap (Dipath.refl y).toDirectedMap where
  toDirectedMap := γ.toDirectedMap.comp MaxDirected
  map_zero_left := fun t => by
    show γ (max 0 t) = _
    have : max 0 t = t := max_eq_right t.2.1
    rw [this]
    rfl
  map_one_left := fun t => by
    show γ (max 1 t) = _
    have : max 1 t = 1 := max_eq_left t.2.2
    rw [this, γ.target]
    rfl
lemma pathToTarget_apply (s t : I) : PathToTarget γ (s, t) = γ (max s t) := rfl
lemma pathToTarget_range : Set.range (PathToTarget γ) = Set.range γ := by
  ext z
  constructor
  · rintro ⟨t, ht⟩
    use max t.1 t.2
    rw [←ht]
    exact (pathToTarget_apply γ t.1 t.2).symm
  · rintro ⟨t, ht⟩
    use (t, t)
    rw [←ht, pathToTarget_apply]
    exact congr_arg γ (max_self t)
end Dihomotopy
end DirectedMap
namespace DihomToPathDihom
variable {X : dTopCat} {f g : D(I, X)}
def dihom_to_dihom_of_paths (F : Dihomotopy f g) :
    Dihomotopy (Dipath.of_directedMap f).toDirectedMap (Dipath.of_directedMap g).toDirectedMap where
  toDirectedMap := F.toDirectedMap
  map_zero_left := fun x => by rw [F.map_zero_left]; rfl
  map_one_left := fun x => by rw [F.map_one_left]; rfl
/--
  Let a dihomotopy `F : f ~ g`, with `f g : D(I, X)` be  given:
    C----- g -----D
    |             |
    |             |
    |             |
    |             |
    A----- f -----B
  Then there is a path-dihomotopy between the paths
    A --refl A--> A --f--> B --F.eval_at_right 1--> D
  and
    A --F.eval_at_right 0--> C --g--> D --refl D--> D
-/
def dihom_to_path_dihom (F : Dihomotopy f g) : Dipath.Dihomotopy
    (((Dipath.refl (f 0)).trans (Dipath.of_directedMap f)).trans (F.eval_at_right 1))
    (((F.eval_at_right 0).trans (Dipath.of_directedMap g)).trans (Dipath.refl (g 1))) where
  toDihomotopy :=
      Dihomotopy.hcomp'
      (
      Dihomotopy.hcomp'
        (DirectedMap.Dihomotopy.SourceToPath (F.eval_at_right 0))
        (dihom_to_dihom_of_paths F)
        (by
          ext s
          show F ((min s 1), 0) = F (s, 0)
          rw [min_eq_left]
          exact s.2.2
        )
      )
      (DirectedMap.Dihomotopy.PathToTarget (F.eval_at_right 1))
      (
        by
          ext s
          show (Dihomotopy.hcomp' _ _ _) (s, 1) = _
          rw [Dihomotopy.hcomp'_apply_one_right]
          show F (s, _ ) = F ((max s 0), 1)
          rw [max_eq_left]
          exact s.2.1
      )
  prop' := fun t x hx => by
    cases hx
    case inl hx => -- x = 0
      subst hx
      show (Dihomotopy.hcomp' _ _ _) (t, 0) = _
      rw [Dihomotopy.hcomp'_apply_zero_right]
      rw [Dihomotopy.hcomp'_apply_zero_right]
      simp
      show F (min t 0, 0) = f 0
      rw [min_eq_right]
      simp
      exact t.2.1
    case inr hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      show (Dihomotopy.hcomp' _ _ _) (t, 1) = _
      rw [Dihomotopy.hcomp'_apply_one_right]
      simp
      show F (max t 1, 1) = g 1
      rw [max_eq_right]
      simp
      exact t.2.2
lemma dihom_to_path_dihom_range (F : Dihomotopy f g) :
    Set.range (dihom_to_path_dihom F) ⊆ Set.range F := by
  unfold dihom_to_path_dihom
  let A := DirectedMap.Dihomotopy.SourceToPath (F.eval_at_right 0)
  let B := dihom_to_dihom_of_paths F
  let C := DirectedMap.Dihomotopy.PathToTarget (F.eval_at_right 1)
  have hA : Set.range A ⊆ Set.range F := by
    dsimp [A]
    rw [DirectedMap.Dihomotopy.sourceToPath_range]
    rintro x ⟨t, ht⟩
    use (t, 0)
    exact ht
  have hB : Set.range B ⊆ Set.range F := fun x h => h
  have hC : Set.range C ⊆ Set.range F := by
    dsimp [C]
    rw [DirectedMap.Dihomotopy.pathToTarget_range]
    rintro x ⟨t, ht⟩
    use (t, 1)
    exact ht
  apply subset_trans (Dihomotopy.hcomp'_range (A.hcomp' B _) C _) (Set.union_subset ?_ hC)
  exact subset_trans (Dihomotopy.hcomp'_range A B _) (Set.union_subset hA hB)
end DihomToPathDihom
end
end Lean4_dihomotopy_to_path_dihomotopy
/-! Source module: Lean4.morphism_aux -/
section Lean4_morphism_aux
/-
  This file contains auxiliary equalities of objects morphisms in a category.
  These are used in the proof of the Van Kampen Theorem in directed_van_kampen.lean
-/
open CategoryTheory
universe u
variable {C C' : CategoryTheory.Cat.{u, u}}
/--
If we have two compositions a --f₀--> b₀ --g₀--> c and a --f₁--> b₁ --g₁--> c,
where b₀ = b₀, f₀ = f₁ and g₀ = g₁, then f₀ ≫ g₀ = f₁ ≫ g₁
-/
lemma eq_of_morphism {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁} {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c}
  (hb : b₁ = b₀) (hf : f₀ = f₁ ≫ (eqToHom hb)) (hg : g₀ = (eqToHom hb.symm) ≫ g₁) :
    f₀ ≫ g₀ = f₁ ≫ g₁ := by
  subst_vars
  rw [eqToHom_refl, Category.comp_id, Category.id_comp]
/--
If two functors are equal, they map objects to the same image
-/
lemma obj_eq_obj_of_eq {F₁ F₂ : C ⥤ C'} (h : F₁ = F₂) (x : C) : F₁.obj x = F₂.obj x :=
  congrFun (congrArg Prefunctor.obj (congrArg Functor.toPrefunctor h)) x
/--
If two functors are equal, they map morphisms to the same image
-/
lemma map_eq_map_of_eq {F₁ F₂ : C ⥤ C'} (h : F₁ = F₂) {x y : C} (f : x ⟶ y) :
    F₁.map f = (eqToHom (obj_eq_obj_of_eq h x)) ≫ F₂.map f ≫ (eqToHom (obj_eq_obj_of_eq h y).symm) := by
  subst_vars
  simp
end Lean4_morphism_aux
/-! Source module: Lean4.path_descent_helpers -/
section Lean4_path_descent_helpers
set_option backward.isDefEq.respectTransparency false
/-
  Constructive path-cover descent for directed fundamental categories.
  This extracted module contains the interval-subdivision and homotopy-grid
  construction used to extend compatible functors across a two-set open cover.
  The classical SVK development specializes the directedness relation to the
  indiscrete preorder and assembles the ordinary groupoid pushout directly from
  these descent lemmas. Source: Directed-Topology-Lean-4, commit
  009529606c66d37ef93b4b81b8587f71ce4d2c56; the retained upstream MIT notice
  is in `Lean4/LICENSE.md`.
-/
universe u v
open Set
open scoped unitInterval Classical FundamentalCategory
attribute [local instance] Dipath.Dihomotopic.setoid
noncomputable section
namespace DirectedVanKampen
open FundamentalCategory DiSubtype CategoryTheory
variable {X : dTopCat.{u}} {X₁ X₂ : Set X}
variable (hX : X₁ ∪ X₂ = Set.univ)
variable (X₁_open : IsOpen X₁) (X₂_open : IsOpen X₂)
-- We will use a shorthand notation for the 4 morphisms in dTop:
-- i₁ : X₁ ∩ X₂ ⟶ X₁
local notation "i₁" => dTopCat.DirectedSubsetHom $ Set.inter_subset_left
-- i₁ : X₁ ∩ X₂ ⟶ X₂
local notation "i₂" => dTopCat.DirectedSubsetHom $ Set.inter_subset_right
-- j₁ : X₁ ⟶ X
local notation "j₁" => dTopCat.DirectedSubtypeHom X₁
-- j₂ : X₂ ⟶ X
local notation "j₂" => dTopCat.DirectedSubtypeHom X₂
namespace PushoutFunctor
open Dipath Dipath.covered Dipath.covered_partwise
variable {x y : X} {C : CategoryTheory.Cat.{u, u}}
variable (F₁ : (dπₓ (dTopCat.of X₁) ⟶ C)) (F₂ : (dπₓ (dTopCat.of X₂) ⟶ C))
variable (h_comm : (dπₘ (dTopCat.DirectedSubsetHom $ Set.inter_subset_left)) ≫ F₁ =
                  ((dπₘ (dTopCat.DirectedSubsetHom $ Set.inter_subset_right)) ≫ F₂))
section FunctorProps
open CategoryTheory
variable {Y : dTopCat.{u}} {Y₀ : Set Y} {F : dπₓ (dTopCat.of Y₀) ⥤ C}
lemma subset_functor_trans {x y z : Y} {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ Y₀) :
    (F.map ⟦SubtypeDipath γ₁ (subsets_of_trans_subset hγ).1⟧ ≫ F.map ⟦SubtypeDipath γ₂ (subsets_of_trans_subset hγ).2⟧) =
      F.map ⟦SubtypeDipath (γ₁.trans γ₂) hγ⟧ := by
  rw [←subtype_trans hγ, Dipath.Dihomotopic.comp_lift]
  exact (F.map_comp _ _).symm
lemma subset_functor_reparam {x y : Y} {γ : Dipath x y} (hγ : range γ ⊆ Y₀) {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    F.map ⟦SubtypeDipath (γ.reparam f hf₀ hf₁)
        (show range (γ.reparam f hf₀ hf₁) ⊆ Y₀ by exact (Dipath.range_reparam γ f hf₀ hf₁).symm ▸ hγ)⟧ =
        F.map ⟦SubtypeDipath γ hγ⟧ := by
  congr 1
  rw [subtype_reparam hγ hf₀ hf₁]
  symm
  exact Quotient.eq.mpr (Dipath.Dihomotopic.reparam (SubtypeDipath γ hγ) f hf₀ hf₁)
lemma functor_cast {X : dTopCat} (F : (dπₓ X) ⥤ C) {x y x' y' : X} (γ : Dipath x y) (hx : x' = x) (hy : y' = y) :
    F.map ⟦γ.cast hx hy⟧ =
      (eqToHom (congrArg F.obj (congrArg FundamentalCategory.mk hx))) ≫ F.map ⟦γ⟧ ≫
      (eqToHom (congrArg F.obj (congrArg FundamentalCategory.mk hy)).symm) := by
  subst_vars
  simp
  congr 2
end FunctorProps
/-
  Given a category C and functors F₁ : dπₓ X₁ ⥤ C and F₂ : dπₓ X₂ ⥤ C, we will construct a functor F : dπₓ X ⥤ C
-/
/- ### Functor on Objects -/
/-
- Define the behaviour on objects
-/
def FunctorOnObj (x : dπₓ X) : C :=
  if hx₁ : x.as ∈ X₁ then
    F₁.toFunctor.obj ⟨x.as, hx₁⟩
  else
    F₂.toFunctor.obj ⟨x.as,
      ((Set.mem_union x.as X₁ X₂).mp (Filter.mem_top.mpr hX x.as)).resolve_left hx₁⟩
-- We will use the shorhand notation F_obj
local notation "F_obj" => FunctorOnObj hX F₁ F₂
/-
  Under the assumption that the square commutes, we can show how the functor behaves on objects
-/
variable {F₁ F₂}
lemma functorOnObj_apply_one (_h_comm : (dπₘ i₁) ≫ F₁ = (dπₘ i₂) ≫ F₂)
    {x : X} (hx : x ∈ X₁) : F₁.toFunctor.obj ⟨x, hx⟩ = F_obj ⟨x⟩ := by
  change F₁.toFunctor.obj ⟨x, hx⟩ =
    (if hx₁ : x ∈ X₁ then F₁.toFunctor.obj ⟨x, hx₁⟩ else _)
  rw [dif_pos hx]
lemma functorOnObj_apply_two (h_comm : (dπₘ i₁) ≫ F₁ = (dπₘ i₂) ≫ F₂)
    {x : X} (hx₂ : x ∈ X₂) : F₂.toFunctor.obj ⟨x, hx₂⟩ = F_obj ⟨x⟩ := by
  by_cases hx₁ : x ∈ X₁
  case pos =>
    have hx₀ : x ∈ X₁ ∩ X₂ := ⟨hx₁, hx₂⟩
    have : F₁.toFunctor.obj ((dπₘ i₁).toFunctor.obj ⟨x, hx₀⟩) = F₂.toFunctor.obj ((dπₘ i₂).toFunctor.obj ⟨x, hx₀⟩) :=
      show ((dπₘ i₁) ≫ F₁).toFunctor.obj ⟨x, hx₀⟩ = ((dπₘ i₂) ≫ F₂).toFunctor.obj ⟨x, hx₀⟩ by rw [h_comm]
    have : F₁.toFunctor.obj ⟨x, hx₁⟩ = F₂.toFunctor.obj (⟨x, hx₂⟩) :=
      calc F₁.toFunctor.obj ⟨x, hx₁⟩
        _ = F₁.toFunctor.obj ((dπₘ i₁).toFunctor.obj ⟨x, hx₀⟩) := rfl
        _ = F₂.toFunctor.obj ((dπₘ i₂).toFunctor.obj ⟨x, hx₀⟩) := this
        _ = F₂.toFunctor.obj (⟨x, hx₂⟩) := rfl
    change F₂.toFunctor.obj ⟨x, hx₂⟩ =
      (if hx : x ∈ X₁ then F₁.toFunctor.obj ⟨x, hx⟩ else _)
    rw [dif_pos hx₁]
    exact this.symm
  case neg =>
    have hx₂' : x ∈ X₂ :=
      ((Set.mem_union x X₁ X₂).mp (Filter.mem_top.mpr hX x)).resolve_left hx₁
    change F₂.toFunctor.obj ⟨x, hx₂⟩ =
      (if hx : x ∈ X₁ then F₁.toFunctor.obj ⟨x, hx⟩ else F₂.toFunctor.obj ⟨x, hx₂'⟩)
    rw [dif_neg hx₁]
/- ### Functor on Maps -/
/-
  Define the mapping behaviour on paths that are fully covered by one set
-/
def FunctorOnHomOfCoveredAux₁ (h_comm : (dπₘ i₁) ≫ F₁ = (dπₘ i₂) ≫ F₂)
    {γ : Dipath x y} (hγ : range γ ⊆ X₁) :
    F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  (eqToHom (functorOnObj_apply_one hX h_comm (source_elt_of_image_subset hγ)).symm) ≫
  (F₁.toFunctor.map ⟦SubtypeDipath γ hγ⟧) ≫
  (eqToHom (functorOnObj_apply_one hX h_comm (target_elt_of_image_subset hγ)))
def FunctorOnHomOfCoveredAux₂ (h_comm : (dπₘ i₁) ≫ F₁ = (dπₘ i₂) ≫ F₂)
    {γ : Dipath x y} (hγ : range γ ⊆ X₂) :
    F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  (eqToHom (functorOnObj_apply_two hX h_comm (source_elt_of_image_subset hγ)).symm) ≫
  (F₂.toFunctor.map ⟦SubtypeDipath γ hγ⟧) ≫
  (eqToHom (functorOnObj_apply_two hX h_comm (target_elt_of_image_subset hγ)))
/-
  Show that these maps respect composition of paths
-/
lemma functorOnHomOfCoveredAux₁_trans {x y z : X} {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₁) :
    FunctorOnHomOfCoveredAux₁ hX h_comm hγ =
      FunctorOnHomOfCoveredAux₁ hX h_comm (subsets_of_trans_subset hγ).1
      ≫ FunctorOnHomOfCoveredAux₁ hX h_comm (subsets_of_trans_subset hγ).2 := by
  unfold FunctorOnHomOfCoveredAux₁
  rw [(subset_functor_trans hγ).symm]
  simp
lemma functorOnHomOfCoveredAux₂_trans {x y z : X} {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₂) :
    FunctorOnHomOfCoveredAux₂ hX h_comm hγ =
      FunctorOnHomOfCoveredAux₂ hX h_comm (subsets_of_trans_subset hγ).1
      ≫ FunctorOnHomOfCoveredAux₂ hX h_comm (subsets_of_trans_subset hγ).2 := by
  unfold FunctorOnHomOfCoveredAux₂
  rw [(subset_functor_trans hγ).symm]
  simp
/-
 Show that the maps respect reparametrization of paths
-/
lemma functorOnHomOfCoveredAux₁_reparam {x y : X} {γ : Dipath x y} (hγ : range γ ⊆ X₁)
  {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    FunctorOnHomOfCoveredAux₁ hX h_comm hγ = FunctorOnHomOfCoveredAux₁ hX h_comm (reparam_subset_of_subset hγ hf₀ hf₁) := by
  unfold FunctorOnHomOfCoveredAux₁
  rw [subset_functor_reparam hγ hf₀ hf₁]
lemma functorOnHomOfCoveredAux₂_reparam {x y : X} {γ : Dipath x y} (hγ : range γ ⊆ X₂)
  {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    FunctorOnHomOfCoveredAux₂ hX h_comm hγ = FunctorOnHomOfCoveredAux₂ hX h_comm (reparam_subset_of_subset hγ hf₀ hf₁) := by
  unfold FunctorOnHomOfCoveredAux₂
  rw [subset_functor_reparam hγ hf₀ hf₁]
/-
 Show that the maps respect reparametrization of paths
-/
lemma functorOnHomOfCoveredAux₁_refl {x : X} (hx : x ∈ X₁) :
  FunctorOnHomOfCoveredAux₁ hX h_comm (range_refl_subset_of_mem hx) = 𝟙 (F_obj ⟨x⟩) := by
  unfold FunctorOnHomOfCoveredAux₁
  rw [subtype_refl, ←id_eq_path_refl, F₁.toFunctor.map_id]
  simp
  all_goals exact hx
lemma functorOnHomOfCoveredAux₂_refl {x : X} (hx : x ∈ X₂) :
  FunctorOnHomOfCoveredAux₂ hX h_comm (range_refl_subset_of_mem hx) = 𝟙 (F_obj ⟨x⟩) := by
  unfold FunctorOnHomOfCoveredAux₂
  rw [subtype_refl, ←id_eq_path_refl, F₂.toFunctor.map_id]
  simp
  all_goals exact hx
/-
  Show that for any path living in X₁ ∩ X₂, it does not matter whether we apply the first or second map
-/
lemma functorOnHomOfCoveredAux_equal {γ : Dipath x y} (hγ₁ : range γ ⊆ X₁) (hγ₂ : range γ ⊆ X₂) :
    FunctorOnHomOfCoveredAux₁ hX h_comm hγ₁ = FunctorOnHomOfCoveredAux₂ hX h_comm hγ₂ := by
  unfold FunctorOnHomOfCoveredAux₁ FunctorOnHomOfCoveredAux₂
  have hγ₀ : range γ ⊆ X₁ ∩ X₂ := subset_inter hγ₁ hγ₂
  apply (eqToHom_comp_iff _ _ _).mpr
  apply (comp_eqToHom_iff _ _ _).mpr
  simp
  exact map_eq_map_of_eq (congrArg CategoryTheory.Cat.Hom.toFunctor h_comm) ⟦SubtypeDipath γ hγ₀⟧
/-
- ### Define the mapping behaviour on covered paths
-/
def FunctorOnHomOfCovered {γ : Dipath x y} (hγ : covered hX γ) :
    F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  Or.by_cases hγ
    (fun hγ => FunctorOnHomOfCoveredAux₁ hX h_comm hγ)
    (fun hγ => FunctorOnHomOfCoveredAux₂ hX h_comm hγ)
local notation "F₀" => FunctorOnHomOfCovered hX h_comm
section FunctorOnHomOfCoveredProperties
lemma functorOnHomOfCovered_apply_left {γ : Dipath x y} (hγ : range γ ⊆ X₁) :
    F₀ (Or.inl hγ) = FunctorOnHomOfCoveredAux₁ hX h_comm hγ := dif_pos hγ
lemma functorOnHomOfCovered_apply_left' {γ : Dipath x y} (hγ : range γ ⊆ X₁) :
    F₀ (covered_partwise_of_covered 0 (Or.inl hγ)) = FunctorOnHomOfCoveredAux₁ hX h_comm hγ :=
  functorOnHomOfCovered_apply_left _ _ _
lemma functorOnHomOfCovered_apply_right {γ : Dipath x y} (hγ : range γ ⊆ X₂) :
    F₀ (Or.inr hγ) = FunctorOnHomOfCoveredAux₂ hX h_comm hγ := by
  by_cases hγ₁ : range γ ⊆ X₁
  · rw [functorOnHomOfCovered_apply_left hX h_comm hγ₁]
    exact functorOnHomOfCoveredAux_equal hX h_comm hγ₁ hγ
  · apply dif_neg hγ₁
lemma functorOnHomOfCovered_equal {γ₁ γ₂ : Dipath x y} (h : γ₁ = γ₂) (hγ₁ : covered hX γ₁) (hγ₂ : covered hX γ₂) :
    F₀ hγ₁ = F₀ hγ₂ := by subst_vars; rfl
lemma functorOnHomOfCovered_refl : F₀ (covered_refl x hX) = 𝟙 (F_obj ⟨x⟩) := by
  cases ((Set.mem_union x X₁ X₂).mp (Filter.mem_top.mpr hX x))
  case inl hx₁ =>
    rw [←functorOnHomOfCoveredAux₁_refl hX h_comm hx₁]
    exact functorOnHomOfCovered_apply_left hX h_comm (DiSubtype.range_refl_subset_of_mem hx₁)
  case inr hx₂ =>
    rw [←functorOnHomOfCoveredAux₂_refl hX h_comm hx₂]
    exact functorOnHomOfCovered_apply_right hX h_comm (DiSubtype.range_refl_subset_of_mem hx₂)
lemma functorOnHomOfCovered_apply_right' {γ : Dipath x y} (hγ : range γ ⊆ X₂) :
    F₀ (covered_partwise_of_covered 0 (Or.inr hγ)) = FunctorOnHomOfCoveredAux₂ hX h_comm hγ :=
  functorOnHomOfCovered_apply_right _ _ _
lemma functorOnHomOfCovered_trans {x y z : X} {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ : covered hX (γ₁.trans γ₂)) :
    F₀ hγ = (F₀ (covered_of_covered_trans hγ).1) ≫ (F₀ (covered_of_covered_trans hγ).2) := by
  cases hγ
  case inl hγ => -- γ is covered by X₁
    rw [functorOnHomOfCovered_apply_left _ _ hγ]
    rw [functorOnHomOfCoveredAux₁_trans]
    congr
    · exact (functorOnHomOfCovered_apply_left _ _ _).symm
    · exact (functorOnHomOfCovered_apply_left _ _ _).symm
  case inr hγ => -- γ is covered by X₂
    rw [functorOnHomOfCovered_apply_right _ _ hγ]
    rw [functorOnHomOfCoveredAux₂_trans]
    congr
    exact (functorOnHomOfCovered_apply_right _ _ (subsets_of_trans_subset hγ).1).symm
    exact (functorOnHomOfCovered_apply_right _ _ (subsets_of_trans_subset hγ).2).symm
lemma functorOnHomOfCovered_reparam {x y : X} {γ : Dipath x y} (hγ : covered hX γ)
  {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    F₀ hγ = F₀ ((covered_reparam_iff γ hX f hf₀ hf₁).mp hγ) := by
  cases hγ
  case inl hγ =>
    have : range (γ.reparam f hf₀ hf₁) ⊆ X₁ := by rw [Dipath.range_reparam γ f hf₀ hf₁]; exact hγ
    rw [functorOnHomOfCovered_apply_left]
    rw [functorOnHomOfCoveredAux₁_reparam hX h_comm hγ hf₀ hf₁]
    rw [←functorOnHomOfCovered_apply_left hX h_comm this]
    assumption
  case inr hγ =>
    have : range (γ.reparam f hf₀ hf₁) ⊆ X₂ := by rw [Dipath.range_reparam γ f hf₀ hf₁]; exact hγ
    rw [functorOnHomOfCovered_apply_right]
    rw [functorOnHomOfCoveredAux₂_reparam hX h_comm hγ hf₀ hf₁]
    rw [←functorOnHomOfCovered_apply_right hX h_comm this]
    assumption
lemma functorOnHomOfCovered_cast {x y x' y' : X} {γ : Dipath x y} (hγ : covered hX γ) (hx : x' = x) (hy : y' = y) :
    F₀ ((covered_cast_iff γ hX hx hy).mp hγ) = (eqToHom (show F_obj ⟨x'⟩ = F_obj ⟨x⟩ by rw [hx])) ≫
      (F₀ hγ) ≫ (eqToHom (show F_obj ⟨y⟩ = F_obj ⟨y'⟩ by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
lemma functorOnHomOfCovered_cast_left {x y x' : X} {γ : Dipath x y} (hγ : covered hX γ) (hx : x' = x) :
    F₀ ((covered_cast_iff γ hX hx rfl).mp hγ) =
      (eqToHom (show F_obj ⟨x'⟩ = F_obj ⟨x⟩ by rw [hx])) ≫ (F₀ hγ) := by
  subst_vars
  rw [eqToHom_refl, Category.id_comp]
lemma functorOnHomOfCovered_cast_right {x y y' : X} {γ : Dipath x y} (hγ : covered hX γ) (hy : y' = y) :
  F₀ ((covered_cast_iff γ hX rfl hy).mp hγ) =
    (F₀ hγ) ≫ (eqToHom (show F_obj ⟨y⟩ = F_obj ⟨y'⟩ by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, Category.comp_id]
lemma functorOnHomOfCovered_split_comp {x y : X} {γ : Dipath x y} (hγ : covered hX γ) {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) :
    F₀ hγ = (F₀ (covered_split_path hT₀ hT₁ hγ).1) ≫ (F₀ (covered_split_path hT₀ hT₁ hγ).2) := by
  have : covered hX ((SplitDipath.FirstPart γ T).trans (SplitDipath.SecondPart γ T)) := by
    rw [SplitDipath.first_trans_second_reparam_eq_self γ hT₀ hT₁] at hγ
    exact (covered_reparam_iff _ hX _ _ _).mpr hγ
  rw [←functorOnHomOfCovered_trans hX h_comm this]
  rw [functorOnHomOfCovered_reparam hX h_comm this
      (SplitDipath.trans_reparam_map_zero hT₀ hT₁)
      (SplitDipath.trans_reparam_map_one hT₀ hT₁)]
  congr
  apply SplitDipath.first_trans_second_reparam_eq_self
lemma functorOnHomOfCovered_dihomotopic {x y : X} {γ γ' : Dipath x y} {F : Dihomotopy γ γ'}
  (hF : Dipath.Dihomotopy.covered hX F) :
    F₀ (Dipath.Dihomotopy.covered_left_of_covered hF) = F₀ (Dipath.Dihomotopy.covered_right_of_covered hF) := by
  cases hF
  case inl hF =>
    have hγ := subset_trans (Dipath.Dihomotopy.range_left_subset F) hF
    have hγ' := subset_trans (Dipath.Dihomotopy.range_right_subset F) hF
    rw [functorOnHomOfCovered_equal hX h_comm rfl _ (Or.inl hγ)]
    rw [functorOnHomOfCovered_equal hX h_comm rfl _ (Or.inl hγ')]
    rw [functorOnHomOfCovered_apply_left hX h_comm hγ]
    rw [functorOnHomOfCovered_apply_left hX h_comm hγ']
    unfold FunctorOnHomOfCoveredAux₁
    rw [dihomSubtype_of_dihom_range_subset hγ hγ' hF]
  case inr hF =>
    have hγ := subset_trans (Dipath.Dihomotopy.range_left_subset F) hF
    have hγ' := subset_trans (Dipath.Dihomotopy.range_right_subset F) hF
    rw [functorOnHomOfCovered_equal hX h_comm rfl _ (Or.inr hγ)]
    rw [functorOnHomOfCovered_equal hX h_comm rfl _ (Or.inr hγ')]
    rw [functorOnHomOfCovered_apply_right hX h_comm hγ]
    rw [functorOnHomOfCovered_apply_right hX h_comm hγ']
    unfold FunctorOnHomOfCoveredAux₂
    rw [dihomSubtype_of_dihom_range_subset hγ hγ' hF]
end FunctorOnHomOfCoveredProperties
/-
-  ### Define the behaviour on partwise covered paths
-/
def FunctorOnHomOfCoveredPartwiseAux {n : ℕ} :
    ∀ (x y : X) (γ : Dipath x y) (_ : covered_partwise hX γ n), F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  Nat.recOn n
    (fun _ _ _ hγ => F₀ hγ)
    (fun _ ih _ _ _ hγ => (F₀ hγ.1) ≫ (ih _ _ _ hγ.2))
abbrev FunctorOnHomOfCoveredPartwise {n : ℕ} {x y : X} {γ : Dipath x y} (hγ : covered_partwise hX γ n) :=
  FunctorOnHomOfCoveredPartwiseAux hX h_comm x y γ hγ
local notation "Fₙ" => FunctorOnHomOfCoveredPartwise hX h_comm
lemma functorOnHomOfCoveredPartwise_apply_0 {x y : X} {γ : Dipath x y} (hγ : covered_partwise hX γ 0) :
    Fₙ hγ = F₀ hγ := rfl
lemma functorOnHomOfCoveredPartwise_apply_succ {n : ℕ} {x y : X} {γ : Dipath x y} (hγ : covered_partwise hX γ n.succ) :
    Fₙ hγ = (F₀ hγ.left) ≫ (Fₙ hγ.right) := rfl
lemma functorOnHomOfCoveredPartwise_equal {n : ℕ} {γ₁ γ₂ : Dipath x y} (h : γ₁ = γ₂)
  (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ n) :
    Fₙ hγ₁ = Fₙ hγ₂ := by subst_vars; rfl
lemma functorOnHomOfCoveredPartwise_equal' {n m : ℕ} {γ₁ γ₂ : Dipath x y} (h₁ : γ₁ = γ₂)
  (h₂ : n = m) (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ m) :
    Fₙ hγ₁ = Fₙ hγ₂ := by subst_vars; rfl
lemma functorOnHomOfCoveredPartwise_cast_params {n m : ℕ} {γ₁ γ₂ : Dipath x y} (h₁ : γ₁ = γ₂)
  (h₂ : n = m) (hγ₁ : covered_partwise hX γ₁ n) :
    Fₙ hγ₁ = Fₙ (covered_partwise_of_equal hX h₁ h₂ hγ₁) := by subst_vars; rfl
lemma functorOnHomOfCoveredPartwise_cast {x y x' y' : X} {n : ℕ} {γ : Dipath x y}
  (hγ : covered_partwise hX γ n) (hx : x' = x) (hy : y' = y) :
    Fₙ ((covered_partwise_cast_iff hX γ hx hy).mp hγ) =
      (eqToHom (by rw [hx])) ≫ (Fₙ hγ) ≫ (eqToHom (by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
  apply functorOnHomOfCoveredPartwise_equal
  rfl
lemma functorOnHomOfCoveredPartwise_cast_left {x y x' : X} {n : ℕ} {γ : Dipath x y}
  (hγ : covered_partwise hX γ n) (hx : x' = x) :
    Fₙ ((covered_partwise_cast_iff hX γ hx rfl).mp hγ) = (eqToHom (by rw [hx])) ≫ (Fₙ hγ) := by
  subst_vars
  rw [eqToHom_refl, Category.id_comp]
  apply functorOnHomOfCoveredPartwise_equal
  rfl
lemma functorOnHomOfCoveredPartwise_cast_right {x y y' : X} {n : ℕ} {γ : Dipath x y} (hγ : covered_partwise hX γ n) (hy : y' = y) :
    Fₙ ((covered_partwise_cast_iff hX γ rfl hy).mp hγ) = (Fₙ hγ) ≫ (eqToHom (by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, Category.comp_id]
  apply functorOnHomOfCoveredPartwise_equal
  rfl
lemma functorOnHomOfCoveredPartwise_refine_of_covered (k : ℕ):
  Π {x y : X} {γ : Dipath x y} (hγ : covered hX γ),
    Fₙ (covered_partwise_of_covered 0 hγ) = Fₙ (covered_partwise_of_covered k hγ) := by
  induction k
  case zero =>
    intro x y γ hγ
    rfl
  case succ k ih =>
    intro x y γ hγ
    rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm (covered_partwise_of_covered k.succ hγ)]
    show (FunctorOnHomOfCovered hX h_comm hγ) = _
    have : 1 < k + 2 := by linarith
    rw [functorOnHomOfCovered_split_comp hX h_comm hγ (Fraction.ofPos_pos (lt_trans zero_lt_one this)) (Fraction.ofPos_lt_one this)]
    congr
    apply ih
    exact (covered_split_path (Fraction.ofPos_pos (lt_trans zero_lt_one this)) (Fraction.ofPos_lt_one this) hγ).2
/--
  When a path is partwise covered by n+1 paths, you can apply Fₙ to both parts of γ, when restricting to
  [0, (d+1)/(n+1)] and [(d+1)/(n+1)]. This lemma states that the composition of these two gives Fₙ γ
-/
lemma functorOnHomOfCoveredPartwise_split {n : ℕ} :
    Π {d : ℕ} (hdn : n > d) {x y : X} {γ : Dipath x y} (hγ : covered_partwise hX γ n),
    Fₙ hγ = Fₙ (covered_partwise_first_part_d hX (Nat.succ_lt_succ hdn) hγ) ≫
          Fₙ (covered_partwise_second_part_d hX (Nat.succ_lt_succ hdn) hγ) := by
  induction n
  case zero =>
    intro d hd
    linarith
  case succ n ih_n =>
    intro d hdn
    induction d
    case zero =>
        intro x y γ hγ
        rfl
    case succ d _ =>
      intro x y γ hγ
      rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm hγ]
      have : n > d := Nat.succ_lt_succ_iff.mp hdn
      rw [ih_n this _]
      rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm _]
      rw [Category.assoc]
      show F₀ _ ≫ (Fₙ _ ≫ Fₙ _) =  F₀ _ ≫ (Fₙ _ ≫ Fₙ _)
      apply eq_of_morphism
      · apply (comp_eqToHom_iff _ _ _).mp
        rw [←functorOnHomOfCovered_cast_right]
        apply functorOnHomOfCovered_equal
        rw [SplitProperties.firstPart_of_firstPart γ (Nat.succ_lt_succ hdn) (Nat.succ_pos d.succ)]
      · rw [←Category.assoc]
        apply eq_of_morphism
        · apply (comp_eqToHom_iff _ _ _).mp
          apply (eqToHom_comp_iff _ _ _).mp
          rw [←functorOnHomOfCoveredPartwise_cast]
          apply functorOnHomOfCoveredPartwise_equal
          rw [SplitProperties.first_part_of_second_part γ (hdn) (Nat.succ_pos d)]
        · rw [←functorOnHomOfCoveredPartwise_cast_left]
          apply functorOnHomOfCoveredPartwise_equal'
          rw [SplitProperties.second_part_of_second_part γ (Nat.lt_of_succ_lt_succ hdn)]
          rw [Nat.succ_sub_succ]
/--
  If a path can be covered partwise by `(n+1) ≥ 2` parts, its refinement by covering it by `k*(n+1)` parts is equal to the composition
  of covering the first part in `k` parts and the second part in `k*n` parts.
-/
lemma functorOnHomOfCoveredPartwise_refine_apply (n k : ℕ) {x y : X} {γ : Dipath x y} (hγ : covered_partwise hX γ n.succ) :
    Fₙ (covered_partwise_refine hX n.succ k hγ) =
      (Fₙ $ covered_partwise_of_covered k hγ.left) ≫ (Fₙ $ covered_partwise_refine hX n k hγ.right) := by
  have h₀ : k + 1 < (n+1+1) * (k + 1) := by
    have : n + 1 + 1 > 1 := by linarith
    convert Nat.mul_lt_mul_of_pos_right (this) (Nat.succ_pos k) using 1
    exact (one_mul k.succ).symm
  have h₁ : (n+1+1)*(k+1) - 1 > (k + 1) - 1 := Nat.pred_lt_pred (ne_of_gt (Nat.succ_pos k)) h₀
  have h₂ := FractionEqualities.cancel_common_factor (Nat.succ_pos k) (le_of_lt (Nat.succ_lt_succ h₁))
  rw [functorOnHomOfCoveredPartwise_split hX h_comm h₁ (covered_partwise_refine hX n.succ k hγ)]
  apply eq_of_morphism
  · rw [←functorOnHomOfCoveredPartwise_cast_right hX h_comm _ (congr_arg γ h₂.symm)]
    apply functorOnHomOfCoveredPartwise_equal hX h_comm
    ext t
    rw [Dipath.cast_apply]
    exact SplitProperties.firstPart_eq_of_point_eq _ h₂.symm _
  · rw [←functorOnHomOfCoveredPartwise_cast_left hX h_comm _ (congr_arg γ h₂.symm)]
    apply functorOnHomOfCoveredPartwise_equal' hX h_comm
    ext t
    rw [Dipath.cast_apply]
    exact SplitProperties.secondPart_eq_of_point_eq _ h₂.symm _
    simp
    rw [Nat.succ_mul, Nat.sub_right_comm, Nat.add_sub_cancel]
lemma functorOnHomOfCoveredPartwise_refine {n : ℕ} (k : ℕ) :
    Π {x y : X} {γ : Dipath x y} (hγ_n : covered_partwise hX γ n),
      Fₙ hγ_n = Fₙ (covered_partwise_refine hX n k hγ_n) := by
  induction n
  case zero => apply functorOnHomOfCoveredPartwise_refine_of_covered
  case succ n ih =>
    intros x y γ hγ
    rw [functorOnHomOfCoveredPartwise_refine_apply hX h_comm n k hγ]
    rw [← functorOnHomOfCoveredPartwise_refine_of_covered hX h_comm _ hγ.left]
    rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm hγ]
    rw [ih hγ.right]
    rfl
lemma functorOnHomOfCoveredPartwise_apply_right_side {x y : X} {γ : Dipath x y} {n : ℕ} (hγ : covered_partwise hX γ n.succ) :
    Fₙ hγ = Fₙ (covered_partwise_first_part_end_split hX hγ) ≫
            F₀ (covered_second_part_end_split hX hγ) := by
  rw [functorOnHomOfCoveredPartwise_split hX h_comm (Nat.lt_succ_self n)]
  rw [functorOnHomOfCoveredPartwise_equal' hX h_comm rfl (Nat.sub_self n.succ)]
  rw [functorOnHomOfCoveredPartwise_apply_0]
lemma functorOnHomOfCoveredPartwise_trans_case_0 {x y z : X} {γ₁ : Dipath x y} {γ₂ : Dipath y z}
  (hγ₁ : covered_partwise hX γ₁ 0) (hγ₂ : covered_partwise hX γ₂ 0) :
    Fₙ (covered_partwise_trans hγ₁ hγ₂) = (Fₙ hγ₁) ≫ (Fₙ hγ₂) := by
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomOfCoveredPartwise_apply_succ]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomOfCovered_equal hX h_comm (SplitProperties.first_part_trans γ₁ γ₂) _ ((covered_cast_iff γ₁ hX _ _).mp hγ₁)]
  rw [functorOnHomOfCovered_equal hX h_comm (SplitProperties.second_part_trans γ₁ γ₂) _ ((covered_cast_iff γ₂ hX _ _).mp hγ₂)]
  rw [functorOnHomOfCovered_cast_right hX h_comm hγ₁]
  rw [functorOnHomOfCovered_cast_left hX h_comm hγ₂]
  simp
lemma functorOnHomOfCoveredPartwise_trans {n : ℕ} :
    Π {x y z : X} {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ n),
      Fₙ (covered_partwise_trans hγ₁ hγ₂) = (Fₙ hγ₁) ≫ (Fₙ hγ₂) := by
  induction n
  case zero =>
    intro x y z γ₁ γ₂ hγ₁ hγ₂
    exact functorOnHomOfCoveredPartwise_trans_case_0 hX h_comm hγ₁ hγ₂
  case succ n ih =>
    intros x y z γ₁ γ₂ hγ₁ hγ₂
    rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm]
    rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm hγ₁]
    rw [Category.assoc]
    apply eq_of_morphism
    · rw [←functorOnHomOfCovered_cast_right]
      apply functorOnHomOfCovered_equal
      ext t
      rw [Dipath.cast_apply]
      exact SplitProperties.trans_first_part γ₁ γ₂ n.succ t
      exact SplitProperties.trans_image_inv_eq_first γ₁ γ₂ n.succ
    · rw [functorOnHomOfCoveredPartwise_apply_right_side hX h_comm hγ₂]
      rw [functorOnHomOfCoveredPartwise_cast_params hX h_comm rfl (Nat.pred_succ n)]
      rw [←Category.assoc (Fₙ _) _ _]
      rw [←ih _ _]
      have : (n.succ + n.succ).succ - 1 = (n + n).succ.succ := by
        rw [Nat.sub_one]
        rw [Nat.pred_succ (n.succ + n.succ)]
        rw [Nat.succ_add]
        rw [Nat.add_succ]
      rw [functorOnHomOfCoveredPartwise_cast_params hX h_comm rfl this]
      rw [←Category.assoc _ _]
      rw [←functorOnHomOfCoveredPartwise_cast_left]
      rw [functorOnHomOfCoveredPartwise_apply_right_side hX h_comm _]
      apply eq_of_morphism
      · rw [←functorOnHomOfCoveredPartwise_cast_right]
        apply functorOnHomOfCoveredPartwise_equal' hX h_comm _ rfl
        pick_goal 3
        ext t
        rw [Dipath.cast_apply]
        rw [Dipath.cast_apply]
        exact SplitProperties.trans_first_part_of_second_part γ₁ γ₂ n t
        exact SplitProperties.trans_image_inv_eq_first γ₁ γ₂ n.succ
        exact SplitProperties.second_part_trans_eval_at_end γ₁ γ₂ n
      · rw [←functorOnHomOfCovered_cast_left]
        apply functorOnHomOfCovered_equal
        ext t
        rw [Dipath.cast_apply]
        exact SplitProperties.trans_second_part_second_part γ₁ γ₂ n t
        exact SplitProperties.second_part_trans_eval_at_end γ₁ γ₂ n
lemma functorOnHomOfCoveredPartwise_unique {n m : ℕ} {γ : Dipath x y}
  (hγ_n : covered_partwise hX γ n) (hγ_m : covered_partwise hX γ m) :
    Fₙ hγ_n = Fₙ hγ_m := by
  rw [functorOnHomOfCoveredPartwise_refine hX h_comm m hγ_n]
  rw [functorOnHomOfCoveredPartwise_refine hX h_comm n hγ_m]
  congr 2
  exact mul_comm _ _
/-
-  ### Define the behaviour on all paths
-/
def FunctorOnHomAux (γ : Dipath x y) : F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  Fₙ (Classical.choose_spec (has_subpaths hX X₁_open X₂_open γ))
local notation "Fh_aux" => FunctorOnHomAux hX X₁_open X₂_open h_comm
lemma functorOnHomAux_apply {n : ℕ} {γ : Dipath x y} (hγ : covered_partwise hX γ n) :
    Fh_aux γ = Fₙ hγ := functorOnHomOfCoveredPartwise_unique hX h_comm _ _
lemma functorOnHomAux_refl {x : X} : Fh_aux (Dipath.refl x) = 𝟙 (F_obj ⟨x⟩) := by
  have : covered_partwise hX (Dipath.refl x) 0 := covered_refl x hX
  rw [functorOnHomAux_apply _ _ _ _ this]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  apply functorOnHomOfCovered_refl
lemma functorOnHomAux_cast {x y x' y' : X} (γ : Dipath x y) (hx : x' = x) (hy : y' = y) :
    Fh_aux (γ.cast hx hy) = (eqToHom (by rw [hx])) ≫ Fh_aux γ ≫ (eqToHom (by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
  apply congr_arg
  ext t
  rfl
lemma functorOnHomAux_trans {x y z : X} (γ₁ : Dipath x y) (γ₂ : Dipath y z) :
    Fh_aux (γ₁.trans γ₂) = Fh_aux γ₁ ≫ Fh_aux γ₂ := by
  cases has_subpaths hX X₁_open X₂_open γ₁
  cases has_subpaths hX X₁_open X₂_open γ₂
  rename_i n hn m hm
  have hn' : covered_partwise hX γ₁ ((n + 1) * (m + 1) - 1) := covered_partwise_refine hX n m hn
  have hm' : covered_partwise hX γ₂ ((n + 1) * (m + 1) - 1) := (mul_comm (m + 1) _) ▸ covered_partwise_refine hX m n hm
  rw [functorOnHomAux_apply hX X₁_open X₂_open h_comm hn']
  rw [functorOnHomAux_apply hX X₁_open X₂_open h_comm hm']
  rw [functorOnHomAux_apply hX X₁_open X₂_open h_comm (covered_partwise_trans hn' hm')]
  rw [functorOnHomOfCoveredPartwise_trans]
lemma functorOnHomAux_split_of_covered_partwise {x y : X} {γ : Dipath x y} {n : ℕ} (hγ : covered_partwise hX γ n.succ) :
    Fh_aux γ =  Fh_aux (SplitDipath.FirstPart γ (Fraction (Nat.succ_pos _) (Nat.succ_le_succ (Nat.zero_le n.succ))))
      ≫ Fh_aux (SplitDipath.SecondPart γ (Fraction (Nat.succ_pos _) (Nat.succ_le_succ (Nat.zero_le n.succ)))) := by
  -- Rewrite L.H.S.
  rw [functorOnHomAux_apply hX _ _ h_comm hγ]
  rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm hγ]
  --Rewrite R.H.S.
  have : covered_partwise hX (SplitDipath.FirstPart γ _) 0 := hγ.left
  rw [functorOnHomAux_apply hX _ _ h_comm this]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomAux_apply hX _ _ h_comm hγ.right]
lemma functorOnHomAux_of_covered_dihomotopic {x y : X} {γ γ' : Dipath x y} {F : Dihomotopy γ γ'}
  (hF : Dipath.Dihomotopy.covered hX F) :
    Fh_aux γ = Fh_aux γ' := by
  have : covered_partwise hX γ 0 := Dipath.Dihomotopy.covered_left_of_covered hF
  rw [functorOnHomAux_apply _ _ _ _ this]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  have : covered_partwise hX γ' 0 := Dipath.Dihomotopy.covered_right_of_covered hF
  rw [functorOnHomAux_apply _ _ _ _ this]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  exact functorOnHomOfCovered_dihomotopic hX h_comm hF
lemma functorOnHomAux_of_homotopic_dimaps_0 {f g : D(I, X)} {H : DirectedMap.Dihomotopy f g}
  (hcov : DirectedMap.Dihomotopy.coveredPartwise hX H 0 0) :
    Fh_aux (Dipath.of_directedMap f) ≫ Fh_aux (H.eval_at_right 1) =
    Fh_aux (H.eval_at_right 0) ≫ Fh_aux (Dipath.of_directedMap g) := by
  let Γ := DihomToPathDihom.dihom_to_path_dihom H
  have Γ_cov : Dipath.Dihomotopy.covered hX Γ := by
    unfold Dipath.Dihomotopy.covered
    cases DirectedMap.Dihomotopy.covered_of_coveredPartwise hcov
    case inl h =>
      left
      exact subset_trans (DihomToPathDihom.dihom_to_path_dihom_range _) h
    case inr h =>
      right
      exact subset_trans (DihomToPathDihom.dihom_to_path_dihom_range _) h
  calc Fh_aux (Dipath.of_directedMap f) ≫ Fh_aux (H.eval_at_right 1)
    _ = (𝟙 (F_obj ⟨f 0⟩) ≫ Fh_aux (of_directedMap f)) ≫ Fh_aux (H.eval_at_right 1)
          := by rw [Category.id_comp]
    _ = (Fh_aux (Dipath.refl (f 0)) ≫ Fh_aux (of_directedMap f)) ≫ Fh_aux (H.eval_at_right 1)
          := by rw [functorOnHomAux_refl]
    _ = Fh_aux ((Dipath.refl (f 0)).trans (of_directedMap f)) ≫ Fh_aux (H.eval_at_right 1)
          := by rw [functorOnHomAux_trans]
    _ = Fh_aux (((Dipath.refl (f 0)).trans (of_directedMap f)).trans (H.eval_at_right 1))
          := by rw [←functorOnHomAux_trans]
    _ = Fh_aux (((H.eval_at_right 0).trans (of_directedMap g)).trans (refl (g 1)))
          := functorOnHomAux_of_covered_dihomotopic hX X₁_open X₂_open h_comm Γ_cov
    _ = Fh_aux ((H.eval_at_right 0).trans (of_directedMap g)) ≫ Fh_aux (refl (g 1))
          := by rw [functorOnHomAux_trans]
    _ = Fh_aux ((H.eval_at_right 0).trans (of_directedMap g)) ≫ 𝟙 (F_obj ⟨g 1⟩)
          := by rw [functorOnHomAux_refl]
    _ = Fh_aux ((H.eval_at_right 0).trans (of_directedMap g))
          := by rw [Category.comp_id]
    _ = Fh_aux (H.eval_at_right 0) ≫ Fh_aux (Dipath.of_directedMap g)
          := by rw [functorOnHomAux_trans]
lemma functorOnHomAux_of_homotopic_dimaps {m : ℕ} :
    Π  {f g : D(I, X)} {H : DirectedMap.Dihomotopy f g} (_ : DirectedMap.Dihomotopy.coveredPartwise hX H 0 m),
      Fh_aux (Dipath.of_directedMap f) ≫ Fh_aux (H.eval_at_right 1) =
      Fh_aux (H.eval_at_right 0) ≫ Fh_aux (Dipath.of_directedMap g) := by
  induction m
  case zero => exact fun hcov => functorOnHomAux_of_homotopic_dimaps_0 _ _ _ _ hcov
  case succ m ih =>
    intro f g H hcov
    have f_cov : covered_partwise hX (Dipath.of_directedMap f) m.succ :=
      DirectedMap.Dihomotopy.path_covered_partiwse_of_dihomotopy_coveredPartwise_left hcov
    have g_cov : covered_partwise hX (Dipath.of_directedMap g) m.succ :=
      DirectedMap.Dihomotopy.path_covered_partiwse_of_dihomotopy_coveredPartwise_right hcov
    -- Split at 1/(m.succ + 1)
    let T := Fraction (Nat.succ_pos m.succ) (Nat.succ_le_succ (Nat.zero_le m.succ))
    let f₁ := (SplitDipath.FirstPart (Dipath.of_directedMap f) T)
    let f₂ := (SplitDipath.SecondPart (Dipath.of_directedMap f) T)
    let g₁ := (SplitDipath.FirstPart (Dipath.of_directedMap g) T)
    let g₂ := (SplitDipath.SecondPart (Dipath.of_directedMap g) T)
    have h₁ : Fh_aux f₂ ≫ Fh_aux (H.eval_at_right 1) = Fh_aux (H.eval_at_right T) ≫ Fh_aux g₂ := by
      have := ih (DirectedMap.Dihomotopy.coveredPartwise_second_hpart hcov)
      have hT : T = Fraction.ofPos (Nat.succ_pos m.succ) := by
        apply Subtype.ext
        simp [T, Fraction.Fraction_coe, Fraction.ofPos_coe]
      rw [SplitDihomotopy.sph_eval_0] at this
      rw [SplitDihomotopy.sph_eval_1] at this
      rw [Dipath.dipath_of_directed_map_of_to_dimap] at this
      rw [Dipath.dipath_of_directed_map_of_to_dimap] at this
      rw [functorOnHomAux_cast] at this
      rw [functorOnHomAux_cast] at this
      rw [functorOnHomAux_cast] at this
      rw [functorOnHomAux_cast] at this
      simp at this
      have := (eqToHom_comp_iff _ _ _).mp this
      rw [←Category.assoc] at this
      have := (comp_eqToHom_iff _ _ _).mp this
      rw [this]
      cases hT
      simp [T, g₂, Category.assoc]
    have h₂ : Fh_aux f₁ ≫ Fh_aux (H.eval_at_right T) = Fh_aux (H.eval_at_right 0) ≫ Fh_aux g₁ := by
      have := functorOnHomAux_of_homotopic_dimaps_0 hX X₁_open X₂_open h_comm
            (DirectedMap.Dihomotopy.coveredPartwise_first_hpart hcov)
      have hT : T = Fraction.ofPos (Nat.succ_pos m.succ) := by
        apply Subtype.ext
        simp [T, Fraction.Fraction_coe, Fraction.ofPos_coe]
      rw [SplitDihomotopy.fph_eval_0] at this
      rw [SplitDihomotopy.fph_eval_1] at this
      rw [Dipath.dipath_of_directed_map_of_to_dimap] at this
      rw [Dipath.dipath_of_directed_map_of_to_dimap] at this
      rw [functorOnHomAux_cast] at this
      rw [functorOnHomAux_cast] at this
      rw [functorOnHomAux_cast] at this
      rw [functorOnHomAux_cast] at this
      simp at this
      have := (eqToHom_comp_iff _ _ _).mp this
      rw [←Category.assoc] at this
      have := (comp_eqToHom_iff _ _ _).mp this
      rw [this]
      cases hT
      simp [T, g₁, Category.assoc]
    calc Fh_aux (Dipath.of_directedMap f) ≫ Fh_aux (H.eval_at_right 1)
      _ = (Fh_aux f₁ ≫ Fh_aux f₂) ≫ Fh_aux (H.eval_at_right 1)
            := by rw [functorOnHomAux_split_of_covered_partwise _ _ _ _ f_cov]
      _ = Fh_aux f₁ ≫ (Fh_aux f₂ ≫ Fh_aux (H.eval_at_right 1))
            := by rw [Category.assoc]
      _ = Fh_aux f₁ ≫ (Fh_aux (H.eval_at_right T) ≫ Fh_aux g₂)
            := by rw [h₁]
      _ = (Fh_aux f₁ ≫ Fh_aux (H.eval_at_right T)) ≫ Fh_aux g₂
            := by rw [Category.assoc]
      _ = (Fh_aux (H.eval_at_right 0) ≫ Fh_aux g₁) ≫ Fh_aux g₂
            := by rw [h₂]
      _ = Fh_aux (H.eval_at_right 0) ≫ (Fh_aux g₁ ≫ Fh_aux g₂)
            := by rw [Category.assoc]
      _ = Fh_aux (H.eval_at_right 0) ≫ Fh_aux (Dipath.of_directedMap g)
            := by rw [functorOnHomAux_split_of_covered_partwise _ _ _ _ g_cov]
lemma functorOnHomAux_of_covered_dihomotopic_zero_m {m : ℕ} {x y : X} {γ γ' : Dipath x y}
  (h : Dipath.Dihomotopy.dihomotopicCovered hX γ γ' 0 m) :
    Fh_aux γ = Fh_aux γ' := by
  cases h
  rename_i G HG
  have h₁ : Fh_aux ((G.eval_at_right 0)) = (eqToHom (by simp)) ≫
            (𝟙 (F_obj ⟨x⟩)) ≫ (eqToHom (by simp)) := by
    have : G.eval_at_right 0 = (Dipath.refl x).cast γ.source γ'.source := by
      ext t
      show G (t, 0) = x
      simp
    rw [this]
    rw [functorOnHomAux_cast]
    rw [functorOnHomAux_refl]
  have h₂ : Fh_aux ((G.eval_at_right 1)) = (eqToHom (by simp)) ≫
            (𝟙 (F_obj ⟨y⟩)) ≫ (eqToHom (by simp)) := by
    have : G.eval_at_right 1 = (Dipath.refl y).cast γ.target γ'.target := by
      ext t
      show G (t, 1) = y
      simp
    rw [this]
    rw [functorOnHomAux_cast]
    rw [functorOnHomAux_refl]
  have := functorOnHomAux_of_homotopic_dimaps hX X₁_open X₂_open h_comm HG
  rw [h₁, h₂] at this
  rw [Dipath.dipath_of_directed_map_of_to_dimap] at this
  rw [Dipath.dipath_of_directed_map_of_to_dimap] at this
  rw [functorOnHomAux_cast] at this
  rw [functorOnHomAux_cast] at this
  simp at this
  have := (comp_eqToHom_iff _ _ _).mp ((eqToHom_comp_iff _ _ _).mp this)
  simp at this
  exact this
lemma functorOnHomAux_of_partwise_covered_dihomotopic :
    Π {n m : ℕ} {x y : X} {γ γ' : Dipath x y} (_ : Dipath.Dihomotopy.dihomotopicCovered hX γ γ' n m),
    Fh_aux γ = Fh_aux γ' := by
  intro n m
  induction n
  case zero =>
    intro x y γ γ' h
    exact functorOnHomAux_of_covered_dihomotopic_zero_m hX X₁_open X₂_open h_comm h
  case succ n ih =>
    rintro x y γ γ' ⟨F, hF⟩
    have ⟨h₁, h₂⟩ := Dipath.Dihomotopy.dihomotopicCovered_split hX hF
    rw [functorOnHomAux_of_covered_dihomotopic_zero_m hX X₁_open X₂_open h_comm h₁]
    exact ih h₂
lemma functorOnHomAux_of_pre_dihomotopic {γ γ' : Dipath x y} (h : γ.PreDihomotopic γ') :
    Fh_aux γ = Fh_aux γ' := by
  rcases Dipath.Dihomotopy.dihomotopicCovered_exists_of_preDihomotopic hX h X₁_open X₂_open with ⟨n, m, h⟩
  exact functorOnHomAux_of_partwise_covered_dihomotopic hX X₁_open X₂_open h_comm h
lemma functorOnHomAux_of_dihomotopic (γ γ' : Dipath x y) (h : γ.Dihomotopic γ') :
    Fh_aux γ = Fh_aux γ' :=
  Relation.EqvGen.rec
    (fun _ _ h => functorOnHomAux_of_pre_dihomotopic _ _ _ _ h)
    (fun _ => rfl)
    (fun _ _ _ h => h.symm)
    (fun _ _ _ _ _ h₁ h₂ => Eq.trans h₁ h₂)
  h
/-
-  ### Define the behaviour on quotient of paths
-/
def FunctorOnHom {x y : dπₓ X} (γ : x ⟶ y) : F_obj x ⟶ F_obj y :=
 Quotient.liftOn γ Fh_aux (functorOnHomAux_of_dihomotopic hX X₁_open X₂_open h_comm)
local notation "F_hom" => FunctorOnHom hX X₁_open X₂_open h_comm
lemma functorOnHom_apply (γ : Dipath x y) :
  F_hom ⟦γ⟧ = Fh_aux γ := rfl
lemma functorOnHom_trans {x y z : X} (γ₁ : Dipath x y) (γ₂ : Dipath y z) :
    F_hom ⟦γ₁.trans γ₂⟧ = F_hom ⟦γ₁⟧ ≫ F_hom ⟦γ₂⟧ := by
  repeat { rw [functorOnHom_apply] }
  exact functorOnHomAux_trans hX X₁_open X₂_open h_comm γ₁ γ₂
lemma functorOnHom_id (x : dπₓ X) : F_hom (𝟙 x) = 𝟙 (F_obj x) := by
  rw [id_eq_path_refl]
  rw [functorOnHom_apply]
  apply functorOnHomAux_refl
lemma functorOnHom_comp_path {x y z  : X} (γ₁ : Dipath x y) (γ₂ : Dipath y z) :
    F_hom (⟦γ₁⟧ ≫ ⟦γ₂⟧) = F_hom ⟦γ₁⟧ ≫ F_hom ⟦γ₂⟧ := by
  rw [functorOnHom_apply]
  rw [functorOnHom_apply]
  rw [comp_eq]
  rw [←Dipath.Dihomotopic.comp_lift]
  exact functorOnHom_trans hX X₁_open X₂_open h_comm γ₁ γ₂
lemma functorOnHom_comp {x y z  : dπₓ X} (γ₁ : x ⟶ y) (γ₂ : y ⟶ z) :
    F_hom (γ₁ ≫ γ₂) = F_hom γ₁ ≫ F_hom γ₂ := by
  have := functorOnHom_comp_path hX X₁_open X₂_open h_comm (γ₁.out) (γ₂.out)
  rw [Quotient.out_eq] at this
  rw [Quotient.out_eq] at this
  exact this
/-
  ## Define the functor F : (dπₓ X) ⟶ C
-/
def Functor : (dπₓ X) ⟶ C where
  toFunctor := {
    obj := F_obj
    map γ := F_hom γ
    map_id x := functorOnHom_id hX X₁_open X₂_open h_comm x
    map_comp γ₁ γ₂ := functorOnHom_comp hX X₁_open X₂_open h_comm γ₁ γ₂
  }
local notation "F" => Functor hX X₁_open X₂_open h_comm
lemma functorObj_def {x : dπₓ X} : (F).toFunctor.obj x = F_obj x := rfl
lemma functorHom_def {x y : dπₓ X} (f : x ⟶ y) : (F).toFunctor.map f = F_hom f := rfl
lemma functor_comp_left_object (x : X₁) : (F).toFunctor.obj ((dπₘ j₁).toFunctor.obj ⟨x⟩) = F₁.toFunctor.obj ⟨x⟩ := by
  show F_obj ⟨j₁ _⟩ = _
  rw [←functorOnObj_apply_one hX h_comm]
  congr 1
  change (x : X) ∈ X₁
  exact x.property
lemma functor_comp_left_dipath {x y : X₁} (γ : Dipath x y) : F_hom ((dπₘ j₁).toFunctor.map ⟦γ⟧) =
    (eqToHom (functor_comp_left_object hX X₁_open X₂_open h_comm x)) ≫ (F₁.toFunctor.map ⟦γ⟧) ≫
    (eqToHom (functor_comp_left_object hX X₁_open X₂_open h_comm y).symm)
     := by
  rw [subtype_path_class_eq_map]
  rw [functorOnHom_apply]
  have h₁ : range (γ.map (DirectedSubtypeInclusion X₁)) ⊆ X₁ := range_dipath_map_inclusion γ
  have h₂ : covered_partwise hX (γ.map (DirectedSubtypeInclusion X₁)) 0 := Or.inl h₁
  rw [functorOnHomAux_apply hX X₁_open X₂_open h_comm h₂]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomOfCovered_apply_left' hX h_comm h₁]
  rw [FunctorOnHomOfCoveredAux₁]
  rw [subtypeDipath_of_included_dipath_eq]
  rw [functor_cast F₁.toFunctor γ]
  simp
/- Shpw that the two obtained triangles commute -/
lemma functor_comp_left : (dπₘ j₁) ≫ F = F₁ := by
  apply CategoryTheory.Cat.ext
  apply CategoryTheory.Functor.ext
  intros x y f
  show F_hom _ = _
  rw [←Quotient.out_eq f]
  rw [functor_comp_left_dipath hX X₁_open X₂_open h_comm f.out]
lemma functor_comp_right_object (x : X₂) : (F).toFunctor.obj ((dπₘ j₂).toFunctor.obj ⟨x⟩) = F₂.toFunctor.obj ⟨x⟩ := by
  show F_obj ⟨j₂ _⟩ = _
  rw [←functorOnObj_apply_two hX h_comm]
  congr 1
  change (x : X) ∈ X₂
  exact x.property
lemma functor_comp_right_dipath {x y : X₂} (γ : Dipath x y) : F_hom ((dπₘ j₂).toFunctor.map ⟦γ⟧) =
    (eqToHom (functor_comp_right_object hX X₁_open X₂_open h_comm x)) ≫ (F₂.toFunctor.map ⟦γ⟧) ≫
    (eqToHom (functor_comp_right_object hX X₁_open X₂_open h_comm y).symm)
     := by
  rw [subtype_path_class_eq_map]
  rw [functorOnHom_apply]
  have h₁ : range (γ.map (DirectedSubtypeInclusion X₂)) ⊆ X₂ := range_dipath_map_inclusion γ
  have h₂ : covered_partwise hX (γ.map (DirectedSubtypeInclusion X₂)) 0 := Or.inr h₁
  rw [functorOnHomAux_apply hX X₁_open X₂_open h_comm h₂]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomOfCovered_apply_right' hX h_comm h₁]
  rw [FunctorOnHomOfCoveredAux₂]
  rw [subtypeDipath_of_included_dipath_eq]
  rw [functor_cast F₂.toFunctor γ]
  simp
lemma functor_comp_right : (dπₘ j₂) ≫ F = F₂ := by
  apply CategoryTheory.Cat.ext
  apply CategoryTheory.Functor.ext
  intros x y f
  show F_hom _ = _
  rw [←Quotient.out_eq f]
  rw [functor_comp_right_dipath hX X₁_open X₂_open h_comm f.out]
lemma functor_uniq_aux_obj (F' : (dπₓ X) ⟶ C) (h₁ : (dπₘ j₁) ≫ F' = F₁) (h₂ : (dπₘ j₂) ≫ F' = F₂) (x : X) :
    F'.toFunctor.obj ⟨x⟩ = (F).toFunctor.obj ⟨x⟩ := by
  rw [functorObj_def]
  cases ((Set.mem_union x X₁ X₂).mp (Filter.mem_top.mpr hX x))
  case inl hx₁ =>
    rw [←functorOnObj_apply_one hX h_comm hx₁]
    rw [obj_eq_obj_of_eq (congrArg CategoryTheory.Cat.Hom.toFunctor h₁.symm)]
    show F'.toFunctor.obj _ = F'.toFunctor.obj _
    apply congrArg
    rfl
  case inr hx₂ =>
    rw [←functorOnObj_apply_two hX h_comm hx₂]
    rw [obj_eq_obj_of_eq (congrArg CategoryTheory.Cat.Hom.toFunctor h₂.symm)]
    show F'.toFunctor.obj _ = F'.toFunctor.obj _
    apply congrArg
    rfl
lemma functor_uniq_of_covered (F' : (dπₓ X) ⟶ C) (h₁ : (dπₘ j₁) ≫ F' = F₁) (h₂ : (dπₘ j₂) ≫ F' = F₂)
  {x y : X} {γ : Dipath x y} (hγ : covered hX γ) :
    F'.toFunctor.map ⟦γ⟧ = (eqToHom (functor_uniq_aux_obj hX X₁_open X₂_open h_comm F' h₁ h₂ x)) ≫
      (F).toFunctor.map ⟦γ⟧ ≫ (eqToHom (functor_uniq_aux_obj hX X₁_open X₂_open h_comm F' h₁ h₂ y).symm) := by
  rw [functorHom_def]
  rw [functorOnHom_apply]
  have : covered_partwise hX γ 0 := hγ
  rw [functorOnHomAux_apply _ _ _ _ this]
  rw [functorOnHomOfCoveredPartwise_apply_0 _ _ this]
  cases hγ
  case inl hγ =>
    rw [functorOnHomOfCovered_apply_left' _ _ hγ]
    unfold FunctorOnHomOfCoveredAux₁
    calc F'.toFunctor.map ⟦γ⟧
      _ = F'.toFunctor.map ((dπₘ j₁).toFunctor.map ⟦SubtypeDipath γ hγ⟧) := (congrArg F'.toFunctor.map (map_subtypeDipath_eq γ hγ)).symm
      _ = (((dπₘ j₁) ≫ F').toFunctor).map ⟦SubtypeDipath γ hγ⟧ := rfl
      _ = _ := by rw [map_eq_map_of_eq (congrArg CategoryTheory.Cat.Hom.toFunctor h₁)]
      _ = _ := by simp
  case inr hγ =>
    rw [functorOnHomOfCovered_apply_right' _ _ hγ]
    unfold FunctorOnHomOfCoveredAux₂
    calc F'.toFunctor.map ⟦γ⟧
      _ = F'.toFunctor.map ((dπₘ j₂).toFunctor.map ⟦SubtypeDipath γ hγ⟧) := (congrArg F'.toFunctor.map (map_subtypeDipath_eq γ hγ)).symm
      _ = (((dπₘ j₂) ≫ F').toFunctor).map ⟦SubtypeDipath γ hγ⟧ := rfl
      _ = _ := by rw [map_eq_map_of_eq (congrArg CategoryTheory.Cat.Hom.toFunctor h₂)]
      _ = _ := by simp
lemma functor_uniq_aux_map (F' : (dπₓ X) ⟶ C) (h₁ : (dπₘ j₁) ≫ F' = F₁) (h₂ : (dπₘ j₂) ≫ F' = F₂) {n : ℕ} :
    Π {x y : X} {γ : Dipath x y} (_ : covered_partwise hX γ n), F'.toFunctor.map ⟦γ⟧ =
      (eqToHom (functor_uniq_aux_obj hX X₁_open X₂_open h_comm F' h₁ h₂ x)) ≫ (F).toFunctor.map ⟦γ⟧
        ≫ (eqToHom (functor_uniq_aux_obj hX X₁_open X₂_open h_comm F' h₁ h₂ y).symm) := by
  induction n
  case zero =>
    intros x y γ hγ
    exact functor_uniq_of_covered _ _ _ _ F' h₁ h₂ hγ
  case succ n ih =>
    intros x y γ hγ
    let T := Fraction (Nat.succ_pos n.succ) (Nat.succ_le_succ (Nat.zero_le n.succ)) -- T = 1/(n+1+1)
    have hT₀ : 0 < T := Fraction.pos_of_pos (zero_lt_one) _
    have hT₁ : T < 1 := Fraction.lt_one_of_lt (zero_le_one) (Nat.succ_lt_succ (Nat.succ_pos n))
    rw [SplitDipath.first_trans_second_reparam_eq_self γ hT₀ hT₁]
    rw [Dipath.Dihomotopic.quot_reparam]
    rw [Dipath.Dihomotopic.comp_lift]
    rw [← comp_eq]
    have hT : T = Fraction.ofPos (Nat.succ_pos n.succ) := by
      apply Subtype.ext
      simp [T, Fraction.Fraction_coe, Fraction.ofPos_coe]
    rw [CategoryTheory.Functor.map_comp]
    rw [CategoryTheory.Functor.map_comp]
    rw [functor_uniq_of_covered hX X₁_open X₂_open h_comm  F' h₁ h₂ hγ.left]
    rw [ih hγ.right]
    cases hT
    simp [T, Category.assoc]
lemma functor_uniq (F' : (dπₓ X) ⟶ C) (h₁ : (dπₘ j₁) ≫ F' = F₁) (h₂ : (dπₘ j₂) ≫ F' = F₂) : F' = F := by
  apply CategoryTheory.Cat.ext
  apply CategoryTheory.Functor.ext
  intros x y f
  rw [←Quotient.out_eq f]
  cases has_subpaths hX X₁_open X₂_open (Quotient.out f)
  rename_i n hn
  exact functor_uniq_aux_map hX X₁_open X₂_open h_comm F' h₁ h₂ hn
end PushoutFunctor
end DirectedVanKampen
end
end Lean4_path_descent_helpers
/-! Source module: ClassicalSVK.Bridge.Categories -/
section ClassicalSVK_Bridge_Categories
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
end ClassicalSVK_Bridge_Categories
/-! Source module: ClassicalSVK.Bridge.Naturality -/
section ClassicalSVK_Bridge_Naturality
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
end ClassicalSVK_Bridge_Naturality
/-! Source module: ClassicalSVK.Bridge.Naturality2 -/
section ClassicalSVK_Bridge_Naturality2
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
end ClassicalSVK_Bridge_Naturality2
/-! Source module: ClassicalSVK.Bridge.Iso -/
section ClassicalSVK_Bridge_Iso
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
end ClassicalSVK_Bridge_Iso
/-! Source module: ClassicalSVK.Pushout -/
section ClassicalSVK_Pushout
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open CategoryTheory.Limits
open scoped unitInterval FundamentalCategory
universe u
namespace ClassicalSVK
theorem classicalOpenCoverPushout
    {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    let i₁ : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U :=
      TopCat.ofHom ⟨(fun x => (⟨x.1, x.2.1⟩ : U)),
        Continuous.subtype_mk continuous_subtype_val (fun x => x.2.1)⟩
    let i₂ : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of V :=
      TopCat.ofHom ⟨(fun x => (⟨x.1, x.2.2⟩ : V)),
        Continuous.subtype_mk continuous_subtype_val (fun x => x.2.2)⟩
    let j₁ : TopCat.of U ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let j₂ : TopCat.of V ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    IsPushout
      (Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map i₁))
      (Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map i₂))
      (Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map j₁))
      (Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map j₂)) := by
  dsimp only
  letI : Preorder X := universalPreorder X
  letI : DirectedSpace X := DirectedSpace.Preorder X
  let i₁ : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U :=
    TopCat.ofHom ⟨(fun x => (⟨x.1, x.2.1⟩ : U)),
      Continuous.subtype_mk continuous_subtype_val (fun x => x.2.1)⟩
  let i₂ : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of V :=
    TopCat.ofHom ⟨(fun x => (⟨x.1, x.2.2⟩ : V)),
      Continuous.subtype_mk continuous_subtype_val (fun x => x.2.2)⟩
  let j₁ : TopCat.of U ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let j₂ : TopCat.of V ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let dI0_1 : dTopCat.of (U ∩ V : Set X) ⟶ dTopCat.of (U : Set X) :=
    dTopCat.DirectedSubsetHom (X := dTopCat.of X) (Y₀ := U ∩ V) (Y₁ := U) Set.inter_subset_left
  let dI0_2 : dTopCat.of (U ∩ V : Set X) ⟶ dTopCat.of (V : Set X) :=
    dTopCat.DirectedSubsetHom (X := dTopCat.of X) (Y₀ := U ∩ V) (Y₁ := V) Set.inter_subset_right
  let dJ0_1 : dTopCat.of (U : Set X) ⟶ dTopCat.of X := dTopCat.DirectedSubtypeHom (X := dTopCat.of X) U
  let dJ0_2 : dTopCat.of (V : Set X) ⟶ dTopCat.of X := dTopCat.DirectedSubtypeHom (X := dTopCat.of X) V
  have hi₁ : i₁ = TopCat.ofHom dI0_1.toContinuousMap := by
    ext x
    rfl
  have hi₂ : i₂ = TopCat.ofHom dI0_2.toContinuousMap := by
    ext x
    rfl
  have hj₁ : j₁ = TopCat.ofHom dJ0_1.toContinuousMap := by
    ext x
    rfl
  have hj₂ : j₂ = TopCat.ofHom dJ0_2.toContinuousMap := by
    ext x
    rfl
  let dI₁ := FundamentalCategory.fundamentalCategoryFunctor.map dI0_1
  let dI₂ := FundamentalCategory.fundamentalCategoryFunctor.map dI0_2
  let dJ₁ := FundamentalCategory.fundamentalCategoryFunctor.map dJ0_1
  let dJ₂ := FundamentalCategory.fundamentalCategoryFunctor.map dJ0_2
  let cI₁ := Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map i₁)
  let cI₂ := Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map i₂)
  let cJ₁ := Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map j₁)
  let cJ₂ := Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map j₂)
  let dToP_I : FundamentalCategory {x : X // x ∈ U ∩ V} ⥤ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of {x : X // x ∈ U ∩ V})) := directedToClassical (X := {x : X // x ∈ U ∩ V})
  let dToP_U : FundamentalCategory U ⥤ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of U)) := directedToClassical (X := U)
  let dToP_V : FundamentalCategory V ⥤ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of V)) := directedToClassical (X := V)
  let dToP_X : FundamentalCategory X ⥤ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) := directedToClassical (X := X)
  let pToD_I : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of {x : X // x ∈ U ∩ V})) ⥤ FundamentalCategory {x : X // x ∈ U ∩ V} := classicalToDirected (X := {x : X // x ∈ U ∩ V})
  let pToD_U : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of U)) ⥤ FundamentalCategory U := classicalToDirected (X := U)
  let pToD_V : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of V)) ⥤ FundamentalCategory V := classicalToDirected (X := V)
  let pToD_X : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) ⥤ FundamentalCategory X := classicalToDirected (X := X)
  let dToP_I_cat : FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of {x : X // x ∈ U ∩ V}) ⟶ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of {x : X // x ∈ U ∩ V})) := ⟨dToP_I⟩
  let dToP_U_cat : FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of U) ⟶ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of U)) := ⟨dToP_U⟩
  let dToP_V_cat : FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of V) ⟶ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of V)) := ⟨dToP_V⟩
  let dToP_X_cat : FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of X) ⟶ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) := ⟨dToP_X⟩
  let pToD_I_cat : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of {x : X // x ∈ U ∩ V})) ⟶ FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of {x : X // x ∈ U ∩ V}) := ⟨pToD_I⟩
  let pToD_U_cat : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of U)) ⟶ FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of U) := ⟨pToD_U⟩
  let pToD_V_cat : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of V)) ⟶ FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of V) := ⟨pToD_V⟩
  let pToD_X_cat : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) ⟶ FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of X) := ⟨pToD_X⟩
  have hi₁_nat : dI₁ ≫ dToP_U_cat = dToP_I_cat ≫ cI₁ := by
    apply Cat.ext
    dsimp [dI₁, dToP_U_cat, dToP_I_cat, cI₁, dToP_U, dToP_I]
    simpa only [← hi₁] using directedToClassical_naturality dI0_1
  have hi₂_nat : dI₂ ≫ dToP_V_cat = dToP_I_cat ≫ cI₂ := by
    apply Cat.ext
    dsimp [dI₂, dToP_V_cat, dToP_I_cat, cI₂, dToP_V, dToP_I]
    simpa only [← hi₂] using directedToClassical_naturality dI0_2
  have hj₁_nat : dJ₁ ≫ dToP_X_cat = dToP_U_cat ≫ cJ₁ := by
    apply Cat.ext
    dsimp [dJ₁, dToP_X_cat, dToP_U_cat, cJ₁, dToP_X, dToP_U]
    simpa only [← hj₁] using directedToClassical_naturality dJ0_1
  have hj₂_nat : dJ₂ ≫ dToP_X_cat = dToP_V_cat ≫ cJ₂ := by
    apply Cat.ext
    dsimp [dJ₂, dToP_X_cat, dToP_V_cat, cJ₂, dToP_X, dToP_V]
    simpa only [← hj₂] using directedToClassical_naturality dJ0_2
  have hi₁_nat' : cI₁ ≫ pToD_U_cat = pToD_I_cat ≫ dI₁ := by
    apply Cat.ext
    dsimp [dI₁, cI₁, pToD_U_cat, pToD_I_cat, pToD_U, pToD_I]
    simpa only [← hi₁] using classicalToDirected_naturality dI0_1
  have hi₂_nat' : cI₂ ≫ pToD_V_cat = pToD_I_cat ≫ dI₂ := by
    apply Cat.ext
    dsimp [dI₂, cI₂, pToD_V_cat, pToD_I_cat, pToD_V, pToD_I]
    simpa only [← hi₂] using classicalToDirected_naturality dI0_2
  have hj₁_nat' : cJ₁ ≫ pToD_X_cat = pToD_U_cat ≫ dJ₁ := by
    apply Cat.ext
    dsimp [dJ₁, cJ₁, pToD_X_cat, pToD_U_cat, pToD_X, pToD_U]
    simpa only [← hj₁] using classicalToDirected_naturality dJ0_1
  have hj₂_nat' : cJ₂ ≫ pToD_X_cat = pToD_V_cat ≫ dJ₂ := by
    apply Cat.ext
    dsimp [dJ₂, cJ₂, pToD_X_cat, pToD_V_cat, pToD_X, pToD_V]
    simpa only [← hj₂] using classicalToDirected_naturality dJ0_2
  have hIsoI : pToD_I_cat ≫ dToP_I_cat = 𝟙 _ := by
    apply Cat.ext
    exact classicalToDirected_comp_directedToClassical
      (X := {x : X // x ∈ U ∩ V})
  have hIsoU : pToD_U_cat ≫ dToP_U_cat = 𝟙 _ := by
    apply Cat.ext
    exact classicalToDirected_comp_directedToClassical (X := U)
  have hIsoV : pToD_V_cat ≫ dToP_V_cat = 𝟙 _ := by
    apply Cat.ext
    exact classicalToDirected_comp_directedToClassical (X := V)
  have hIsoX : pToD_X_cat ≫ dToP_X_cat = 𝟙 _ := by
    apply Cat.ext
    exact classicalToDirected_comp_directedToClassical (X := X)
  have hpathDescent : IsPushout dI₁ dI₂ dJ₁ dJ₂ := by
    -- Construct the descent functor directly. Its action on each path is
    -- defined by an open-cover subdivision; independence of the subdivision
    -- and of the path-homotopy representative is established by the interval
    -- and square subdivision lemmas in `PushoutFunctor`.
    apply PushoutAlternative.isPushout_alternative
    · rw [← Functor.map_comp, ← Functor.map_comp]
      change FundamentalCategory.fundamentalCategoryFunctor.map (dI0_1 ≫ dJ0_1) =
        FundamentalCategory.fundamentalCategoryFunctor.map (dI0_2 ≫ dJ0_2)
      congr 1
    intro C F₁ F₂ h_comm
    let descent := DirectedVanKampen.PushoutFunctor.Functor hUV hU hV h_comm
    use descent
    constructor
    constructor
    · exact DirectedVanKampen.PushoutFunctor.functor_comp_left hUV hU hV h_comm
    · exact DirectedVanKampen.PushoutFunctor.functor_comp_right hUV hU hV h_comm
    · rintro F' ⟨h₁, h₂⟩
      exact DirectedVanKampen.PushoutFunctor.functor_uniq hUV hU hV h_comm F' h₁ h₂
  have hcomm : cI₁ ≫ cJ₁ = cI₂ ≫ cJ₂ := by
    calc
      cI₁ ≫ cJ₁ = (pToD_I_cat ≫ dToP_I_cat) ≫ (cI₁ ≫ cJ₁) := by
        rw [hIsoI]
        simp
      _ = pToD_I_cat ≫ ((dToP_I_cat ≫ cI₁) ≫ cJ₁) := by simp [Category.assoc]
      _ = pToD_I_cat ≫ ((dI₁ ≫ dToP_U_cat) ≫ cJ₁) := by rw [← hi₁_nat]
      _ = pToD_I_cat ≫ (dI₁ ≫ (dToP_U_cat ≫ cJ₁)) := by simp [Category.assoc]
      _ = pToD_I_cat ≫ (dI₁ ≫ (dJ₁ ≫ dToP_X_cat)) := by rw [← hj₁_nat]
      _ = pToD_I_cat ≫ ((dI₁ ≫ dJ₁) ≫ dToP_X_cat) := by simp [Category.assoc]
      _ = pToD_I_cat ≫ ((dI₂ ≫ dJ₂) ≫ dToP_X_cat) := by
        exact congrArg (fun f => pToD_I_cat ≫ f ≫ dToP_X_cat) hpathDescent.w
      _ = pToD_I_cat ≫ (dI₂ ≫ (dJ₂ ≫ dToP_X_cat)) := by simp [Category.assoc]
      _ = pToD_I_cat ≫ (dI₂ ≫ (dToP_V_cat ≫ cJ₂)) := by rw [hj₂_nat]
      _ = pToD_I_cat ≫ ((dI₂ ≫ dToP_V_cat) ≫ cJ₂) := by simp [Category.assoc]
      _ = pToD_I_cat ≫ ((dToP_I_cat ≫ cI₂) ≫ cJ₂) := by rw [hi₂_nat]
      _ = (pToD_I_cat ≫ dToP_I_cat) ≫ (cI₂ ≫ cJ₂) := by simp [Category.assoc]
      _ = cI₂ ≫ cJ₂ := by
        rw [hIsoI]
        simp
  let cP : PushoutCocone cI₁ cI₂ := PushoutCocone.mk cJ₁ cJ₂ hcomm
  let toDirectedCocone : PushoutCocone cI₁ cI₂ → PushoutCocone dI₁ dI₂ := fun s =>
    PushoutCocone.mk (dToP_U_cat ≫ s.inl) (dToP_V_cat ≫ s.inr) (by
      calc
        dI₁ ≫ (dToP_U_cat ≫ s.inl) = (dI₁ ≫ dToP_U_cat) ≫ s.inl := by simp [Category.assoc]
        _ = (dToP_I_cat ≫ cI₁) ≫ s.inl := by rw [hi₁_nat]
        _ = dToP_I_cat ≫ (cI₁ ≫ s.inl) := by simp [Category.assoc]
        _ = dToP_I_cat ≫ (cI₂ ≫ s.inr) := by exact congrArg (fun f => dToP_I_cat ≫ f) s.condition
        _ = (dToP_I_cat ≫ cI₂) ≫ s.inr := by simp [Category.assoc]
        _ = (dI₂ ≫ dToP_V_cat) ≫ s.inr := by rw [← hi₂_nat]
        _ = dI₂ ≫ (dToP_V_cat ≫ s.inr) := by simp [Category.assoc])
  let liftDesc : ∀ s : PushoutCocone cI₁ cI₂,
      Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) ⟶ s.pt := fun s => by
    exact pToD_X_cat ≫ PushoutCocone.IsColimit.desc hpathDescent.isColimit
      (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition
  have hcolim : IsColimit cP := by
    change IsColimit (PushoutCocone.mk cJ₁ cJ₂ hcomm)
    refine PushoutCocone.IsColimit.mk (f := cI₁) (g := cI₂) (inl := cJ₁) (inr := cJ₂) hcomm liftDesc ?_ ?_ ?_
    · intro s
      let desc := PushoutCocone.IsColimit.desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition
      calc
        cJ₁ ≫ liftDesc s = cJ₁ ≫ (pToD_X_cat ≫ desc) := rfl
        _ = (cJ₁ ≫ pToD_X_cat) ≫ desc := by simp [Category.assoc]
        _ = (pToD_U_cat ≫ dJ₁) ≫ desc := by rw [hj₁_nat']
        _ = pToD_U_cat ≫ (dJ₁ ≫ desc) := by simp [Category.assoc]
        _ = pToD_U_cat ≫ ((toDirectedCocone s).inl) := by
          exact congrArg (fun f => pToD_U_cat ≫ f)
            (PushoutCocone.IsColimit.inl_desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition)
        _ = (pToD_U_cat ≫ dToP_U_cat) ≫ s.inl := by simp [toDirectedCocone, Category.assoc]
        _ = s.inl := by rw [hIsoU]; simp
    · intro s
      let desc := PushoutCocone.IsColimit.desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition
      calc
        cJ₂ ≫ liftDesc s = cJ₂ ≫ (pToD_X_cat ≫ desc) := rfl
        _ = (cJ₂ ≫ pToD_X_cat) ≫ desc := by simp [Category.assoc]
        _ = (pToD_V_cat ≫ dJ₂) ≫ desc := by rw [hj₂_nat']
        _ = pToD_V_cat ≫ (dJ₂ ≫ desc) := by simp [Category.assoc]
        _ = pToD_V_cat ≫ ((toDirectedCocone s).inr) := by
          exact congrArg (fun f => pToD_V_cat ≫ f)
            (PushoutCocone.IsColimit.inr_desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition)
        _ = (pToD_V_cat ≫ dToP_V_cat) ≫ s.inr := by simp [toDirectedCocone, Category.assoc]
        _ = s.inr := by rw [hIsoV]; simp
    · intro s m hm₁ hm₂
      let desc := PushoutCocone.IsColimit.desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition
      have hmap : dToP_X_cat ≫ m = desc := by
        have hleft : dJ₁ ≫ (dToP_X_cat ≫ m) = dJ₁ ≫ desc := by
          calc
            dJ₁ ≫ (dToP_X_cat ≫ m) = (dJ₁ ≫ dToP_X_cat) ≫ m := by simp [Category.assoc]
            _ = (dToP_U_cat ≫ cJ₁) ≫ m := by rw [hj₁_nat]
            _ = dToP_U_cat ≫ (cJ₁ ≫ m) := by simp [Category.assoc]
            _ = dToP_U_cat ≫ s.inl := by exact congrArg (fun f => dToP_U_cat ≫ f) hm₁
            _ = dJ₁ ≫ desc := by
              exact (PushoutCocone.IsColimit.inl_desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition).symm
        have hright : dJ₂ ≫ (dToP_X_cat ≫ m) = dJ₂ ≫ desc := by
          calc
            dJ₂ ≫ (dToP_X_cat ≫ m) = (dJ₂ ≫ dToP_X_cat) ≫ m := by simp [Category.assoc]
            _ = (dToP_V_cat ≫ cJ₂) ≫ m := by rw [hj₂_nat]
            _ = dToP_V_cat ≫ (cJ₂ ≫ m) := by simp [Category.assoc]
            _ = dToP_V_cat ≫ s.inr := by exact congrArg (fun f => dToP_V_cat ≫ f) hm₂
            _ = dJ₂ ≫ desc := by
              exact (PushoutCocone.IsColimit.inr_desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition).symm
        exact PushoutCocone.IsColimit.hom_ext hpathDescent.isColimit hleft hright
      calc
        m = 𝟙 _ ≫ m := by simp
        _ = (pToD_X_cat ≫ dToP_X_cat) ≫ m := by rw [hIsoX]
        _ = pToD_X_cat ≫ (dToP_X_cat ≫ m) := by simp [Category.assoc]
        _ = pToD_X_cat ≫ desc := by rw [hmap]
  exact IsPushout.of_isColimit hcolim
end ClassicalSVK
end ClassicalSVK_Pushout
/-! Source module: CellAttachment.CoverPushout -/
section CellAttachment_CoverPushout
/-! # Van Kampen on the actual disk-center/interior open cover -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
/-- The actual intersection of the two quotient open sets. -/
def overlap (f : ι → C(Circle, X)) : Set (Space f) :=
  puncturedNeighborhood f ∩ interiors f
/-- Actual overlap inclusion into the punctured neighborhood. -/
def overlapLeft (f : ι → C(Circle, X)) : C(overlap f, puncturedNeighborhood f) :=
  ⟨fun y => ⟨y.1,y.2.1⟩, continuous_subtype_val.subtype_mk _⟩
/-- Actual overlap inclusion into the disk interiors. -/
def overlapRight (f : ι → C(Circle, X)) : C(overlap f, interiors f) :=
  ⟨fun y => ⟨y.1,y.2.2⟩, continuous_subtype_val.subtype_mk _⟩
/-- The actual inclusion of the punctured neighborhood into the quotient. -/
def neighborhoodToSpace (f : ι → C(Circle, X)) : C(puncturedNeighborhood f, Space f) :=
  ⟨Subtype.val,continuous_subtype_val⟩
/-- The actual inclusion of all disk interiors into the quotient. -/
def interiorsToSpace (f : ι → C(Circle, X)) : C(interiors f, Space f) :=
  ⟨Subtype.val,continuous_subtype_val⟩
/-- The established ordinary all-object fundamental-groupoid SVK theorem is
applied to proved open sets in the genuine adjunction quotient. -/
theorem coverPushout (f : ι → C(Circle, X)) :
    IsPushout (FundamentalGroupoid.map (overlapLeft f)).toCatHom
      (FundamentalGroupoid.map (overlapRight f)).toCatHom
      (FundamentalGroupoid.map (neighborhoodToSpace f)).toCatHom
      (FundamentalGroupoid.map (interiorsToSpace f)).toCatHom := by
  exact ClassicalSVK.classicalOpenCoverPushout (puncturedNeighborhood f) (interiors f)
    (puncturedNeighborhood_isOpen f) (interiors_isOpen f) (openCover_union f)
end CellAttachment
end
end CellAttachment_CoverPushout
/-! Source module: CellAttachment.Radial -/
section CellAttachment_Radial
/-! # Explicit radial deformation of the punctured closed disk -/
noncomputable section
open scoped unitInterval
namespace CellAttachment
abbrev PuncturedDisk := {z : Disk // (z : ℂ) ≠ 0}
/-- The complex coordinate of a punctured disk point. -/
def puncturedCoordinate : C(PuncturedDisk, ℂ) :=
  ⟨fun z => z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩
lemma punctured_norm_pos (z : PuncturedDisk) : 0 < ‖puncturedCoordinate z‖ :=
  norm_pos_iff.mpr z.property
lemma punctured_norm_le_one (z : PuncturedDisk) : ‖puncturedCoordinate z‖ ≤ 1 :=
  z.1.property
/-- Normalize a nonzero disk point to the actual unit circle. -/
def polar : C(PuncturedDisk, Circle) where
  toFun z := ⟨(‖puncturedCoordinate z‖⁻¹ : ℝ) • puncturedCoordinate z, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀]
    exact ne_of_gt (punctured_norm_pos z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((puncturedCoordinate.continuous.norm.inv₀
      (fun z => ne_of_gt (punctured_norm_pos z))).smul puncturedCoordinate.continuous)
/-- The radial expansion coefficient at a homotopy time. -/
def radialCoefficient (t : unitInterval) (z : PuncturedDisk) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) * ‖puncturedCoordinate z‖⁻¹
lemma radialCoefficient_mul_norm (t : unitInterval) (z : PuncturedDisk) :
    radialCoefficient t z * ‖puncturedCoordinate z‖ =
      (1 - (t : ℝ)) * ‖puncturedCoordinate z‖ + (t : ℝ) := by
  unfold radialCoefficient
  rw [add_mul, mul_assoc, inv_mul_cancel₀ (ne_of_gt (punctured_norm_pos z)), mul_one]
lemma radialCoefficient_pos (t : unitInterval) (z : PuncturedDisk) :
    0 < radialCoefficient t z := by
  have hr := punctured_norm_pos z
  have hr1 := punctured_norm_le_one z
  have hm : (t : ℝ) * ‖puncturedCoordinate z‖ ≤ (t : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hr1 t.property.1
  have hprod : 0 < radialCoefficient t z * ‖puncturedCoordinate z‖ := by
    rw [radialCoefficient_mul_norm]
    nlinarith [t.property.1]
  exact (mul_pos_iff_of_pos_right hr).mp hprod
lemma radialCoefficient_mul_norm_le_one (t : unitInterval) (z : PuncturedDisk) :
    radialCoefficient t z * ‖puncturedCoordinate z‖ ≤ 1 := by
  rw [radialCoefficient_mul_norm]
  have h := mul_le_mul_of_nonneg_left (punctured_norm_le_one z)
    (sub_nonneg.mpr t.property.2)
  nlinarith
/-- The radial deformation stays within the genuine punctured closed disk. -/
def radialDeformation (t : unitInterval) (z : PuncturedDisk) : PuncturedDisk :=
  ⟨⟨radialCoefficient t z • puncturedCoordinate z, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (radialCoefficient_pos t z)]
      exact radialCoefficient_mul_norm_le_one t z⟩,
    smul_ne_zero (ne_of_gt (radialCoefficient_pos t z)) z.property⟩
lemma radialDeformation_continuous :
    Continuous (fun p : unitInterval × PuncturedDisk => radialDeformation p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous ((fun p : unitInterval × PuncturedDisk => radialCoefficient p.1 p.2) •
    (fun p : unitInterval × PuncturedDisk => puncturedCoordinate p.2))
  apply Continuous.smul
  · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((puncturedCoordinate.continuous.comp continuous_snd).norm.inv₀
          (fun p => ne_of_gt (punctured_norm_pos p.2))))
  · exact puncturedCoordinate.continuous.comp continuous_snd
@[simp] lemma radialDeformation_zero (z : PuncturedDisk) : radialDeformation 0 z = z := by
  apply Subtype.ext
  apply Subtype.ext
  simp [radialDeformation, radialCoefficient, puncturedCoordinate]
@[simp] lemma radialDeformation_one_coordinate (z : PuncturedDisk) :
    (radialDeformation 1 z).1.1 = (polar z : ℂ) := by
  change radialCoefficient 1 z • puncturedCoordinate z = ‖puncturedCoordinate z‖⁻¹ • puncturedCoordinate z
  simp [radialCoefficient]
/-- Every boundary point stays fixed throughout the radial deformation. -/
lemma radialDeformation_boundary_fixed (t : unitInterval) (z : PuncturedDisk)
    (h : ‖puncturedCoordinate z‖ = 1) : radialDeformation t z = z := by
  apply Subtype.ext
  apply Subtype.ext
  change radialCoefficient t z • puncturedCoordinate z = puncturedCoordinate z
  simp [radialCoefficient, h]
/-- Positive radial expansion leaves the actual polar circle point unchanged. -/
@[simp] lemma polar_radialDeformation (t : unitInterval) (z : PuncturedDisk) :
    polar (radialDeformation t z) = polar z := by
  apply Circle.ext
  change ‖radialCoefficient t z • puncturedCoordinate z‖⁻¹ •
    (radialCoefficient t z • puncturedCoordinate z) =
      ‖puncturedCoordinate z‖⁻¹ • puncturedCoordinate z
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (radialCoefficient_pos t z), smul_smul]
  congr 1
  field_simp [ne_of_gt (radialCoefficient_pos t z), ne_of_gt (punctured_norm_pos z)]
end CellAttachment
end
end CellAttachment_Radial
/-! Source module: CellAttachment.RawNeighborhood -/
section CellAttachment_RawNeighborhood
/-! # The punctured raw coproduct and its genuine quotient map -/
noncomputable section
namespace CellAttachment
universe u v
open Topology
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
abbrev PuncturedRaw (X : Type u) (ι : Type v) := X ⊕ (Σ _ : ι, PuncturedDisk)
/-- Forget the nonzero condition while keeping the coproduct topology. -/
def puncturedRawInclusion : PuncturedRaw X ι → Raw X ι :=
  Sum.map id (Sigma.map id (fun _ => Subtype.val))
lemma puncturedDisk_isOpen : IsOpen {z : Disk | (z : ℂ) ≠ 0} :=
  isOpen_ne.preimage continuous_subtype_val
lemma puncturedSigmaInclusion_isOpenEmbedding :
    IsOpenEmbedding (Sigma.map id (fun _ : ι => Subtype.val) :
      (Σ _ : ι, PuncturedDisk) → (Σ _ : ι, Disk)) :=
  (isOpenEmbedding_sigmaMap Function.injective_id).mpr
    (fun _ => puncturedDisk_isOpen.isOpenEmbedding_subtypeVal)
lemma puncturedRawInclusion_isOpenEmbedding :
    IsOpenEmbedding (puncturedRawInclusion : PuncturedRaw X ι → Raw X ι) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_id.sumMap puncturedSigmaInclusion_isOpenEmbedding.continuous
  · exact Sum.map_injective.mpr ⟨Function.injective_id,
      puncturedSigmaInclusion_isOpenEmbedding.injective⟩
  · exact IsOpenMap.id.sumMap puncturedSigmaInclusion_isOpenEmbedding.isOpenMap
lemma puncturedRawInclusion_mem (f : ι → C(Circle, X)) (a : PuncturedRaw X ι) :
    quotientMap f (puncturedRawInclusion a) ∈ puncturedNeighborhood f := by
  cases a with
  | inl x => exact inclusion_not_mem_centers f x
  | inr z =>
    rcases z with ⟨i, z⟩
    change quotientMap f (.inr ⟨i, z.1⟩) ∉ centers f
    rw [quotient_inr_mem_centers]
    exact z.property
/-- The punctured coproduct is exactly the open preimage of the punctured neighborhood. -/
def puncturedRawEquiv (f : ι → C(Circle, X)) :
    PuncturedRaw X ι ≃ (quotientMap f ⁻¹' puncturedNeighborhood f) where
  toFun a := ⟨puncturedRawInclusion a, puncturedRawInclusion_mem f a⟩
  invFun
    | ⟨.inl x, _⟩ => .inl x
    | ⟨.inr ⟨i, z⟩, h⟩ => .inr ⟨i, ⟨z, by
        exact (quotient_inr_mem_centers f i z).not.mp h⟩⟩
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with ⟨a,h⟩; cases a <;> rfl
/-- Its topology is the actual subspace topology of the raw coproduct. -/
def puncturedRawHomeomorph (f : ι → C(Circle, X)) :
    PuncturedRaw X ι ≃ₜ (quotientMap f ⁻¹' puncturedNeighborhood f) :=
  (puncturedRawEquiv f).toHomeomorphOfIsInducing
    (puncturedRawInclusion_isOpenEmbedding.isEmbedding.codRestrict
      _ (puncturedRawInclusion_mem f)).isInducing
/-- The quotient onto the punctured neighborhood, with all disk punctures genuine. -/
def puncturedQuotient (f : ι → C(Circle, X)) : C(PuncturedRaw X ι, puncturedNeighborhood f) where
  toFun a := ⟨quotientMap f (puncturedRawInclusion a), puncturedRawInclusion_mem f a⟩
  continuous_toFun := Continuous.subtype_mk
    ((quotientMap f).continuous.comp puncturedRawInclusion_isOpenEmbedding.continuous) _
lemma puncturedQuotient_isQuotientMap (f : ι → C(Circle, X)) :
    IsQuotientMap (puncturedQuotient f) := by
  have hq := (quotientMap_isQuotientMap f).restrictPreimage_isOpen
    (puncturedNeighborhood_isOpen f)
  exact hq.comp (puncturedRawHomeomorph f).isQuotientMap
end CellAttachment
end
end CellAttachment_RawNeighborhood
/-! Source module: CellAttachment.Retraction -/
section CellAttachment_Retraction
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
end
end CellAttachment_Retraction
/-! Source module: CellAttachment.CoverModels -/
section CellAttachment_CoverModels
/-! # Coordinate models of the genuine cover and its overlap
The interior open set is the actual coproduct of open disks; its intersection
with the punctured neighborhood is the actual coproduct of punctured open
disks. Component indices are locally constant and hence cannot change along
any path or fundamental-groupoid arrow.
-/
noncomputable section
open scoped ContinuousMap
namespace CellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
theorem overlap_isOpen (f : ι → C(Circle, X)) : IsOpen (overlap f) :=
  (puncturedNeighborhood_isOpen f).inter (interiors_isOpen f)
/-- Forget puncturing while retaining the actual open-disk point. -/
def annulusInclusion : C(Annulus, OpenDisk) := ⟨Subtype.val, continuous_subtype_val⟩
/-- The coproduct of punctured-disk inclusions. -/
def sigmaAnnulusInclusion : C((Σ _ : ι, Annulus), (Σ _ : ι, OpenDisk)) :=
  ⟨Sigma.map id (fun _ => annulusInclusion), Continuous.sigma_map
    (fun _ => annulusInclusion.continuous)⟩
lemma sigmaAnnulusInclusion_isEmbedding :
    Topology.IsEmbedding (sigmaAnnulusInclusion (ι := ι)) := by
  change Topology.IsEmbedding (Sigma.map (β₁ := fun _ : ι => Annulus) (β₂ := fun _ : ι => OpenDisk)
    (id : ι → ι) (fun _ => (Subtype.val : Annulus → OpenDisk)))
  exact (Topology.isEmbedding_sigmaMap Function.injective_id).mpr
    (fun _ => Topology.IsEmbedding.subtypeVal)
/-- Coordinates of punctured interior points in the actual quotient space. -/
def annulusInteriorMap (f : ι → C(Circle, X)) : C((Σ _ : ι, Annulus), Space f) :=
  (interiorMap f).comp sigmaAnnulusInclusion
@[simp] lemma annulusInteriorMap_apply (f : ι → C(Circle, X))
    (z : Σ _ : ι, Annulus) : annulusInteriorMap f z = interiorMap f ⟨z.1, z.2.1⟩ := rfl
lemma annulusInteriorMap_isEmbedding (f : ι → C(Circle, X)) :
    Topology.IsEmbedding (annulusInteriorMap f) :=
  (interiorMap_isOpenEmbedding f).isEmbedding.comp sigmaAnnulusInclusion_isEmbedding
/-- An interior coordinate belongs to the punctured neighborhood exactly when it is nonzero. -/
@[simp] lemma interiorMap_mem_puncturedNeighborhood_iff (f : ι → C(Circle, X))
    (i : ι) (z : OpenDisk) :
    interiorMap f ⟨i, z⟩ ∈ puncturedNeighborhood f ↔ (z : ℂ) ≠ 0 := by
  change quotientMap f (.inr ⟨i, ⟨z, z.property.le⟩⟩) ∉ centers f ↔ _
  simp only [quotient_inr_mem_centers]
/-- No assumed topology: the image of the actual punctured-disk embedding is the overlap. -/
lemma annulusInteriorMap_range (f : ι → C(Circle, X)) :
    Set.range (annulusInteriorMap f) = overlap f := by
  ext y
  constructor
  · rintro ⟨⟨i, z⟩, rfl⟩
    exact ⟨(interiorMap_mem_puncturedNeighborhood_iff f i z.1).mpr z.property,
      interiorRepresentative_mem_interiors f i z.1⟩
  · intro hy
    have hy' : y ∈ Set.range (interiorMap f) := by
      rw [interiorMap_range]
      exact hy.2
    obtain ⟨⟨i, z⟩, rfl⟩ := hy'
    have hz : (z : ℂ) ≠ 0 :=
      (interiorMap_mem_puncturedNeighborhood_iff f i z).mp hy.1
    exact ⟨⟨i, ⟨z, hz⟩⟩, rfl⟩
/-- The overlap, with its genuine induced quotient topology, is the annulus coproduct. -/
def overlapHomeomorph (f : ι → C(Circle, X)) :
    (Σ _ : ι, Annulus) ≃ₜ overlap f :=
  (annulusInteriorMap_isEmbedding f).toHomeomorph.trans
    (Homeomorph.setCongr (annulusInteriorMap_range f))
@[simp] lemma overlapHomeomorph_apply (f : ι → C(Circle, X))
    (z : Σ _ : ι, Annulus) : (overlapHomeomorph f z : Space f) = annulusInteriorMap f z := rfl
/-- The actual continuous inclusion of the overlap into the interior open set. -/
def overlapToInteriors (f : ι → C(Circle, X)) : C(overlap f, interiors f) :=
  ⟨fun z => ⟨z.1, z.property.2⟩, continuous_subtype_val.subtype_mk _⟩
/-- The actual continuous inclusion of the overlap into the punctured neighborhood. -/
def overlapToNeighborhood (f : ι → C(Circle, X)) : C(overlap f, puncturedNeighborhood f) :=
  ⟨fun z => ⟨z.1, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩
/-- The coordinate square of the overlap inclusion commutes on the nose. -/
lemma overlapToInteriors_coordinates (f : ι → C(Circle, X))
    (z : Σ _ : ι, Annulus) :
    overlapToInteriors f (overlapHomeomorph f z) =
      interiorsHomeomorph f (sigmaAnnulusInclusion z) := rfl
/-- A single disk's actual open embedding into the quotient. -/
def cellInteriorMap (f : ι → C(Circle, X)) (i : ι) : C(OpenDisk, Space f) :=
  ⟨fun z => interiorMap f ⟨i, z⟩,
    (interiorMap f).continuous.comp continuous_sigmaMk⟩
/-- The genuine interior of an individual attached cell. -/
def cellInterior (f : ι → C(Circle, X)) (i : ι) : Set (Space f) :=
  Set.range (cellInteriorMap f i)
lemma cellInteriorMap_isOpenEmbedding (f : ι → C(Circle, X)) (i : ι) :
    Topology.IsOpenEmbedding (cellInteriorMap f i) :=
  (interiorMap_isOpenEmbedding f).comp Topology.IsOpenEmbedding.sigmaMk
lemma cellInterior_isOpen (f : ι → C(Circle, X)) (i : ι) : IsOpen (cellInterior f i) :=
  (cellInteriorMap_isOpenEmbedding f i).isOpen_range
/-- Each actual interior component is homeomorphic to the genuine open complex disk. -/
def cellInteriorHomeomorph (f : ι → C(Circle, X)) (i : ι) : OpenDisk ≃ₜ cellInterior f i :=
  (cellInteriorMap_isOpenEmbedding f i).isEmbedding.toHomeomorph
@[simp] lemma cellInteriorHomeomorph_apply (f : ι → C(Circle, X)) (i : ι) (z : OpenDisk) :
    (cellInteriorHomeomorph f i z : Space f) = cellInteriorMap f i z := rfl
/-- Contractibility of the actual quotient-subspace cell interior follows from its coordinates. -/
instance cellInterior_contractibleSpace (f : ι → C(Circle, X)) (i : ι) :
    ContractibleSpace (cellInterior f i) :=
  (cellInteriorHomeomorph f i).symm.contractibleSpace
instance cellInterior_simplyConnectedSpace (f : ι → C(Circle, X)) (i : ι) :
    SimplyConnectedSpace (cellInterior f i) := inferInstance
/-- A single punctured disk's actual embedding into the quotient. -/
def cellAnnulusMap (f : ι → C(Circle, X)) (i : ι) : C(Annulus, Space f) :=
  (cellInteriorMap f i).comp annulusInclusion
/-- The genuine overlap component in cell `i`. -/
def cellOverlap (f : ι → C(Circle, X)) (i : ι) : Set (Space f) :=
  overlap f ∩ cellInterior f i
lemma cellOverlap_isOpen (f : ι → C(Circle, X)) (i : ι) : IsOpen (cellOverlap f i) :=
  (overlap_isOpen f).inter (cellInterior_isOpen f i)
lemma cellAnnulusMap_isEmbedding (f : ι → C(Circle, X)) (i : ι) :
    Topology.IsEmbedding (cellAnnulusMap f i) :=
  (cellInteriorMap_isOpenEmbedding f i).isEmbedding.comp Topology.IsEmbedding.subtypeVal
lemma cellAnnulusMap_range (f : ι → C(Circle, X)) (i : ι) :
    Set.range (cellAnnulusMap f i) = cellOverlap f i := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨?_, ⟨z.1, rfl⟩⟩
    rw [← annulusInteriorMap_range]
    exact ⟨⟨i, z⟩, rfl⟩
  · intro hy
    obtain ⟨z, rfl⟩ := hy.2
    have hz : (z : ℂ) ≠ 0 :=
      (interiorMap_mem_puncturedNeighborhood_iff f i z).mp hy.1.1
    exact ⟨⟨z, hz⟩, rfl⟩
/-- Each actual overlap component is homeomorphic to the genuine punctured open disk. -/
def cellOverlapHomeomorph (f : ι → C(Circle, X)) (i : ι) : Annulus ≃ₜ cellOverlap f i :=
  (cellAnnulusMap_isEmbedding f i).toHomeomorph.trans
    (Homeomorph.setCongr (cellAnnulusMap_range f i))
@[simp] lemma cellOverlapHomeomorph_apply (f : ι → C(Circle, X)) (i : ι) (z : Annulus) :
    (cellOverlapHomeomorph f i z : Space f) = cellAnnulusMap f i z := rfl
instance cellOverlap_pathConnectedSpace (f : ι → C(Circle, X)) (i : ι) :
    PathConnectedSpace (cellOverlap f i) :=
  (cellOverlapHomeomorph f i).pathConnectedSpace
/-- The actual overlap component has its circle homotopy type by proved geometry. -/
def cellOverlapHomotopyEquivCircle (f : ι → C(Circle, X)) (i : ι) :
    cellOverlap f i ≃ₕ Circle :=
  (cellOverlapHomeomorph f i).symm.toHomotopyEquiv.trans annulusHomotopyEquivCircle
/-- The actual half-radius basepoint in cell `i`'s overlap. -/
def cellOverlapBasepoint (f : ι → C(Circle, X)) (i : ι) : cellOverlap f i :=
  cellOverlapHomeomorph f i annulusBasepoint
/-- The concrete half-radius loop in the actual quotient overlap component. -/
def cellOverlapGenerator (f : ι → C(Circle, X)) (i : ι) :
    Path (cellOverlapBasepoint f i) (cellOverlapBasepoint f i) :=
  annulusGenerator.map (cellOverlapHomeomorph f i).continuous
/-- Its actual based homotopy class. -/
def cellOverlapGeneratorClass (f : ι → C(Circle, X)) (i : ι) :
    FundamentalGroup (cellOverlap f i) (cellOverlapBasepoint f i) :=
  .mk (cellOverlapGenerator f i)
/-- Coordinate transport is the induced isomorphism of actual based fundamental groups. -/
def cellOverlapFundamentalGroupEquivAnnulus (f : ι → C(Circle, X)) (i : ι) :
    FundamentalGroup (cellOverlap f i) (cellOverlapBasepoint f i) ≃*
      FundamentalGroup Annulus annulusBasepoint :=
  homotopyEquivFundamentalGroupOfEq (cellOverlapHomeomorph f i).symm.toHomotopyEquiv
    ((cellOverlapHomeomorph f i).symm_apply_apply annulusBasepoint)
set_option backward.isDefEq.respectTransparency false in
@[simp] lemma cellOverlapFundamentalGroupEquivAnnulus_generator
    (f : ι → C(Circle, X)) (i : ι) :
    cellOverlapFundamentalGroupEquivAnnulus f i (cellOverlapGeneratorClass f i) =
      annulusGeneratorClass := by
  change FundamentalGroup.mapOfEq
    ((cellOverlapHomeomorph f i).symm : C(cellOverlap f i, Annulus))
    ((cellOverlapHomeomorph f i).symm_apply_apply annulusBasepoint)
    (cellOverlapGeneratorClass f i) = _
  unfold cellOverlapGeneratorClass cellOverlapGenerator
  rw [FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk
    (((cellOverlapGenerator f i).map (cellOverlapHomeomorph f i).symm.continuous).cast
      ((cellOverlapHomeomorph f i).symm_apply_apply annulusBasepoint).symm
      ((cellOverlapHomeomorph f i).symm_apply_apply annulusBasepoint).symm) = _
  congr 1
  apply Path.ext
  funext t
  exact (cellOverlapHomeomorph f i).symm_apply_apply (annulusGenerator t)
/-- Every actual overlap-component class is a power of the concrete half-radius loop. -/
theorem cellOverlapGenerator_generates (f : ι → C(Circle, X)) (i : ι)
    (γ : FundamentalGroup (cellOverlap f i) (cellOverlapBasepoint f i)) :
    ∃ n : ℤ, cellOverlapGeneratorClass f i ^ n = γ := by
  obtain ⟨n, hn⟩ := annulusGenerator_generates (cellOverlapFundamentalGroupEquivAnnulus f i γ)
  refine ⟨n, (cellOverlapFundamentalGroupEquivAnnulus f i).injective ?_⟩
  rw [map_zpow, cellOverlapFundamentalGroupEquivAnnulus_generator]
  exact hn
lemma cellInterior_subset_interiors (f : ι → C(Circle, X)) (i : ι) :
    cellInterior f i ⊆ interiors f := by
  rintro y ⟨z, rfl⟩
  exact interiorRepresentative_mem_interiors f i z
/-- A cell interior included into the full interior open set. -/
def cellInteriorToInteriors (f : ι → C(Circle, X)) (i : ι) :
    C(cellInterior f i, interiors f) :=
  ⟨fun z => ⟨z.1, cellInterior_subset_interiors f i z.property⟩,
    continuous_subtype_val.subtype_mk _⟩
/-- An overlap component included into the full overlap. -/
def cellOverlapToOverlap (f : ι → C(Circle, X)) (i : ι) :
    C(cellOverlap f i, overlap f) :=
  ⟨fun z => ⟨z.1, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩
/-- An overlap component included into its actual disk interior. -/
def cellOverlapToCellInterior (f : ι → C(Circle, X)) (i : ι) :
    C(cellOverlap f i, cellInterior f i) :=
  ⟨fun z => ⟨z.1, z.property.2⟩, continuous_subtype_val.subtype_mk _⟩
/-- An overlap component included into the actual punctured neighborhood. -/
def cellOverlapToNeighborhood (f : ι → C(Circle, X)) (i : ι) :
    C(cellOverlap f i, puncturedNeighborhood f) :=
  (overlapToNeighborhood f).comp (cellOverlapToOverlap f i)
@[simp] lemma cellInteriorToInteriors_coordinates (f : ι → C(Circle, X)) (i : ι)
    (z : OpenDisk) :
    cellInteriorToInteriors f i (cellInteriorHomeomorph f i z) =
      interiorsHomeomorph f ⟨i, z⟩ := rfl
@[simp] lemma cellOverlapToOverlap_coordinates (f : ι → C(Circle, X)) (i : ι)
    (z : Annulus) :
    cellOverlapToOverlap f i (cellOverlapHomeomorph f i z) =
      overlapHomeomorph f ⟨i, z⟩ := rfl
@[simp] lemma cellOverlapToCellInterior_coordinates (f : ι → C(Circle, X)) (i : ι)
    (z : Annulus) :
    cellOverlapToCellInterior f i (cellOverlapHomeomorph f i z) =
      cellInteriorHomeomorph f i z.1 := rfl
/-- The neighborhood retraction on the overlap is exactly the original attaching map
applied to the polar coordinate, not an abstract homotopic replacement. -/
lemma neighborhoodRetraction_overlap_coordinates (f : ι → C(Circle, X)) (x₀ : X)
    (i : ι) (z : Annulus) :
    neighborhoodRetraction f x₀
      (overlapToNeighborhood f (overlapHomeomorph f ⟨i, z⟩)) = f i (annulusPolar z) := by
  change (if h : (z.1 : ℂ) ≠ 0 then f i (polar ⟨⟨z.1, z.1.property.le⟩, h⟩)
    else x₀) = _
  rw [dite_eq_left z.property]
  rfl
lemma neighborhoodRetraction_cellOverlap_coordinates (f : ι → C(Circle, X)) (x₀ : X)
    (i : ι) (z : Annulus) :
    neighborhoodRetraction f x₀
      (cellOverlapToNeighborhood f i (cellOverlapHomeomorph f i z)) = f i (annulusPolar z) :=
  neighborhoodRetraction_overlap_coordinates f x₀ i z
/-- The index projection from any topological coproduct is locally constant,
without giving the index type any additional structure. -/
lemma sigmaIndex_isLocallyConstant {A : ι → Type*} [∀ i, TopologicalSpace (A i)] :
    IsLocallyConstant (Sigma.fst : (Σ i, A i) → ι) :=
  fun S => isOpen_sigma_fst_preimage S
/-- The cell index of an actual interior point. -/
def interiorIndex (f : ι → C(Circle, X)) (z : interiors f) : ι :=
  ((interiorsHomeomorph f).symm z).1
/-- The cell index of an actual overlap point. -/
def overlapIndex (f : ι → C(Circle, X)) (z : overlap f) : ι :=
  ((overlapHomeomorph f).symm z).1
lemma interiorIndex_isLocallyConstant (f : ι → C(Circle, X)) :
    IsLocallyConstant (interiorIndex f) :=
  sigmaIndex_isLocallyConstant.comp_continuous (interiorsHomeomorph f).symm.continuous
lemma overlapIndex_isLocallyConstant (f : ι → C(Circle, X)) :
    IsLocallyConstant (overlapIndex f) :=
  sigmaIndex_isLocallyConstant.comp_continuous (overlapHomeomorph f).symm.continuous
@[simp] lemma interiorIndex_coordinates (f : ι → C(Circle, X))
    (z : Σ _ : ι, OpenDisk) : interiorIndex f (interiorsHomeomorph f z) = z.1 := by
  simp [interiorIndex]
@[simp] lemma overlapIndex_coordinates (f : ι → C(Circle, X))
    (z : Σ _ : ι, Annulus) : overlapIndex f (overlapHomeomorph f z) = z.1 := by
  simp [overlapIndex]
lemma interiorIndex_overlapToInteriors (f : ι → C(Circle, X)) (z : overlap f) :
    interiorIndex f (overlapToInteriors f z) = overlapIndex f z := by
  obtain ⟨z, rfl⟩ := (overlapHomeomorph f).surjective z
  rw [overlapToInteriors_coordinates, interiorIndex_coordinates, overlapIndex_coordinates]
  rfl
/-- A locally constant index cannot change anywhere along a continuous path. -/
lemma index_constant_along_path {A : Type*} [TopologicalSpace A] {j : A → ι}
    (hj : IsLocallyConstant j) {a b : A} (p : Path a b) (t : unitInterval) : j (p t) = j a := by
  have h := (hj.comp_continuous p.continuous).apply_eq_of_preconnectedSpace t 0
  simpa only [Function.comp_apply, p.source] using h
lemma interiorIndex_path (f : ι → C(Circle, X)) {a b : interiors f}
    (p : Path a b) (t : unitInterval) : interiorIndex f (p t) = interiorIndex f a :=
  index_constant_along_path (interiorIndex_isLocallyConstant f) p t
lemma overlapIndex_path (f : ι → C(Circle, X)) {a b : overlap f}
    (p : Path a b) (t : unitInterval) : overlapIndex f (p t) = overlapIndex f a :=
  index_constant_along_path (overlapIndex_isLocallyConstant f) p t
/-- Every actual interior groupoid arrow lies within a single disk component. -/
lemma interiorIndex_arrow (f : ι → C(Circle, X)) {a b : interiors f}
    (γ : Path.Homotopic.Quotient a b) : interiorIndex f a = interiorIndex f b := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
  simpa only [p.target] using (interiorIndex_path f p 1).symm
/-- Every actual overlap groupoid arrow lies within a single annulus component. -/
lemma overlapIndex_arrow (f : ι → C(Circle, X)) {a b : overlap f}
    (γ : Path.Homotopic.Quotient a b) : overlapIndex f a = overlapIndex f b := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
  simpa only [p.target] using (overlapIndex_path f p 1).symm
/-- The continuous second-coordinate projection of a constant-fiber coproduct. -/
def coproductSecond {A : Type*} [TopologicalSpace A] : C((Σ _ : ι, A), A) :=
  ⟨Sigma.snd, continuous_sigma (fun _ => continuous_id)⟩
/-- The continuous inclusion of one coproduct component. -/
def coproductComponent {A : Type*} [TopologicalSpace A] (i : ι) : C(A, (Σ _ : ι, A)) :=
  ⟨fun z : A => (⟨i, z⟩ : Σ _ : ι, A), by
    exact continuous_sigmaMk (σ := fun _ : ι => A) (i := i)⟩
/-- Mapping a loop in a coproduct component to its coordinate and back changes no path. -/
lemma coproduct_path_reconstruction {A : Type*} [TopologicalSpace A] (i : ι) (a : A)
    (p : Path (⟨i, a⟩ : Σ _ : ι, A) ⟨i, a⟩) :
    (p.map (coproductSecond (ι := ι)).continuous).map (coproductComponent i).continuous = p := by
  apply Path.ext
  funext t
  have hi : (p t).1 = i := index_constant_along_path sigmaIndex_isLocallyConstant p t
  exact Sigma.ext hi.symm (heq_of_eq rfl)
/-- Inclusion of one component induces the actual isomorphism on its based fundamental group. -/
def coproductFundamentalGroupEquiv {A : Type*} [TopologicalSpace A] (i : ι) (a : A) :
    FundamentalGroup A a ≃* FundamentalGroup (Σ _ : ι, A) ⟨i, a⟩ :=
  MulEquiv.ofBijective (FundamentalGroup.map (coproductComponent i) a) (by
    constructor
    · intro γ δ h
      have hr (ε : FundamentalGroup A a) :
          FundamentalGroup.map (coproductSecond (ι := ι)) ⟨i, a⟩
            (FundamentalGroup.map (coproductComponent i) a ε) = ε := by
        obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective ε
        change Path.Homotopic.Quotient.mk
          ((p.map (coproductComponent i).continuous).map (coproductSecond (ι := ι)).continuous) = _
        rfl
      have hh := congrArg (FundamentalGroup.map (coproductSecond (ι := ι)) ⟨i, a⟩) h
      exact (hr γ).symm.trans (hh.trans (hr δ))
    · intro γ
      obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
      refine ⟨Path.Homotopic.Quotient.mk (p.map (coproductSecond (ι := ι)).continuous), ?_⟩
      change Path.Homotopic.Quotient.mk
        ((p.map (coproductSecond (ι := ι)).continuous).map (coproductComponent i).continuous) = _
      rw [coproduct_path_reconstruction]
      rfl)
@[simp] lemma coproductFundamentalGroupEquiv_apply {A : Type*} [TopologicalSpace A]
    (i : ι) (a : A) (γ : FundamentalGroup A a) :
    coproductFundamentalGroupEquiv i a γ = FundamentalGroup.map (coproductComponent i) a γ := rfl
/-- The radius-half anchor of the actual full overlap in cell `i`. -/
def overlapAnchor (f : ι → C(Circle, X)) (i : ι) : overlap f :=
  overlapHomeomorph f ⟨i, annulusBasepoint⟩
/-- An actual path from its component's half-radius anchor to every overlap point. -/
def overlapAnchorPaths (f : ι → C(Circle, X)) (w : overlap f) :
    Path (overlapAnchor f (overlapIndex f w)) w :=
  ((PathConnectedSpace.somePath annulusBasepoint ((overlapHomeomorph f).symm w).2).map
    ((overlapHomeomorph f).continuous.comp (continuous_sigmaMk (i := overlapIndex f w)))).cast
      rfl ((overlapHomeomorph f).apply_symm_apply w).symm
/-- An actual path from the overlap anchor to every point of its disk component. -/
def interiorAnchorPaths (f : ι → C(Circle, X)) (v : interiors f) :
    Path (overlapRight f (overlapAnchor f (interiorIndex f v))) v :=
  ((PathConnectedSpace.somePath annulusBasepoint.1 ((interiorsHomeomorph f).symm v).2).map
    ((interiorsHomeomorph f).continuous.comp (continuous_sigmaMk (i := interiorIndex f v)))).cast
      rfl ((interiorsHomeomorph f).apply_symm_apply v).symm
/-- The full interior open set has trivial vertex groups, even when it is disconnected. -/
theorem interiorVertexGroup_subsingleton (f : ι → C(Circle, X)) (v : interiors f) :
    Subsingleton (FundamentalGroup (interiors f) v) := by
  let h := interiorsHomeomorph f
  let c := h.symm v
  let e := (homotopyEquivFundamentalGroup h.symm.toHomotopyEquiv v).trans
    (coproductFundamentalGroupEquiv c.1 c.2).symm
  exact e.injective.subsingleton
/-- The concrete half-radius generator in the actual full overlap. -/
def overlapAnchorGenerator (f : ι → C(Circle, X)) (i : ι) :
    Path (overlapAnchor f i) (overlapAnchor f i) :=
  annulusGenerator.map
    ((overlapHomeomorph f).continuous.comp (continuous_sigmaMk (i := i)))
/-- Its actual homotopy class at the overlap anchor. -/
def overlapAnchorGeneratorClass (f : ι → C(Circle, X)) (i : ι) :
    FundamentalGroup (overlap f) (overlapAnchor f i) :=
  .mk (overlapAnchorGenerator f i)
/-- Component inclusion followed by the true overlap homeomorphism is an actual based isomorphism. -/
def overlapAnchorFundamentalGroupEquiv (f : ι → C(Circle, X)) (i : ι) :
    FundamentalGroup Annulus annulusBasepoint ≃*
      FundamentalGroup (overlap f) (overlapAnchor f i) :=
  (coproductFundamentalGroupEquiv i annulusBasepoint).trans
    (homotopyEquivFundamentalGroup (overlapHomeomorph f).toHomotopyEquiv ⟨i, annulusBasepoint⟩)
@[simp] lemma overlapAnchorFundamentalGroupEquiv_generator (f : ι → C(Circle, X)) (i : ι) :
    overlapAnchorFundamentalGroupEquiv f i annulusGeneratorClass = overlapAnchorGeneratorClass f i := by
  change Path.Homotopic.Quotient.mk
    ((annulusGenerator.map (coproductComponent i).continuous).map
      (overlapHomeomorph f).continuous) = _
  rfl
/-- Every actual full-overlap anchor loop class is a power of its concrete half-radius generator. -/
theorem overlapAnchorGenerator_generates (f : ι → C(Circle, X)) (i : ι)
    (γ : FundamentalGroup (overlap f) (overlapAnchor f i)) :
    ∃ n : ℤ, γ = overlapAnchorGeneratorClass f i ^ n := by
  obtain ⟨n, hn⟩ := annulusGenerator_generates ((overlapAnchorFundamentalGroupEquiv f i).symm γ)
  refine ⟨n, ?_⟩
  have h := congrArg (overlapAnchorFundamentalGroupEquiv f i) hn
  simpa only [map_zpow, overlapAnchorFundamentalGroupEquiv_generator,
    MulEquiv.apply_symm_apply] using h.symm
/-- The retracted overlap anchor is exactly the attaching map's basepoint. -/
@[simp] lemma neighborhoodRetraction_overlapAnchor (f : ι → C(Circle, X)) (x₀ : X) (i : ι) :
    neighborhoodRetraction f x₀ (overlapLeft f (overlapAnchor f i)) = f i 1 := by
  change neighborhoodRetraction f x₀
    (overlapToNeighborhood f (overlapHomeomorph f ⟨i, annulusBasepoint⟩)) = _
  rw [neighborhoodRetraction_overlap_coordinates, annulusPolar_basepoint]
/-- The actual overlap generator retracts to the original attaching-circle loop,
with its actual endpoint equality displayed explicitly. -/
lemma neighborhoodRetraction_overlapAnchorGenerator (f : ι → C(Circle, X)) (x₀ : X) (i : ι) :
    ((overlapAnchorGenerator f i).map
      ((neighborhoodRetraction f x₀).comp (overlapLeft f)).continuous).cast
        (neighborhoodRetraction_overlapAnchor f x₀ i).symm
        (neighborhoodRetraction_overlapAnchor f x₀ i).symm =
      circleGenerator.map (f i).continuous := by
  apply Path.ext
  funext t
  change neighborhoodRetraction f x₀
    (overlapToNeighborhood f (overlapHomeomorph f ⟨i, annulusGenerator t⟩)) = f i (circleGenerator t)
  rw [neighborhoodRetraction_overlap_coordinates]
  exact congrArg (f i) (annulusPolar_halfCircle (circleGenerator t))
/-- The induced based map sends the actual overlap generator to the attaching class. -/
lemma neighborhoodRetraction_overlapAnchorGeneratorClass
    (f : ι → C(Circle, X)) (x₀ : X) (i : ι) :
    FundamentalGroup.mapOfEq ((neighborhoodRetraction f x₀).comp (overlapLeft f))
      (neighborhoodRetraction_overlapAnchor f x₀ i) (overlapAnchorGeneratorClass f i) =
      FundamentalGroup.map (f i) 1 circleGeneratorClass := by
  rw [FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk
    (((overlapAnchorGenerator f i).map
      ((neighborhoodRetraction f x₀).comp (overlapLeft f)).continuous).cast
        (neighborhoodRetraction_overlapAnchor f x₀ i).symm
        (neighborhoodRetraction_overlapAnchor f x₀ i).symm) = _
  rw [neighborhoodRetraction_overlapAnchorGenerator]
  rfl
end CellAttachment
end
end CellAttachment_CoverModels
/-! Source module: CellAttachment.Deformation -/
section CellAttachment_Deformation
/-!
# Jointly continuous radial deformation on the genuine adjunction quotient
Continuity is descended from the actual punctured quotient using local compactness
of the interval. No global openness of the quotient map is assumed.
-/
noncomputable section
open scoped unitInterval
namespace CellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
/-- Expand each punctured disk radially while fixing the original space and centers. -/
def rawRadial (t : unitInterval) : Raw X ι → Raw X ι
  | .inl x => .inl x
  | .inr ⟨i,z⟩ => if h : (z : ℂ) ≠ 0 then .inr ⟨i,(radialDeformation t ⟨z,h⟩).1⟩
      else .inr ⟨i,z⟩
lemma rawRadial_respects (f : ι → C(Circle, X)) (t : unitInterval)
    {a b : Raw X ι} (h : AttachingRel f a b) :
    AttachingRel f (rawRadial t a) (rawRadial t b) := by
  cases h with
  | boundary i z =>
    change AttachingRel f
      (if h : (z : ℂ) ≠ 0 then .inr ⟨i,(radialDeformation t ⟨boundaryInclusion z,h⟩).1⟩
        else .inr ⟨i,boundaryInclusion z⟩) (.inl (f i z))
    rw [dite_eq_left (Circle.coe_ne_zero z),
      radialDeformation_boundary_fixed t _ (Circle.norm_coe z)]
    exact .boundary i z
/-- Algebraic radial descent; joint continuity on the punctured neighborhood is proved below. -/
def quotientRadial (f : ι → C(Circle, X)) (t : unitInterval) : Space f → Space f :=
  Quot.map (rawRadial t) (fun _ _ h => rawRadial_respects f t h)
@[simp] lemma quotientRadial_inclusion (f : ι → C(Circle, X)) (t : unitInterval) (x : X) :
    quotientRadial f t (inclusion f x) = inclusion f x := rfl
lemma quotientRadial_puncturedQuotient (f : ι → C(Circle, X)) (t : unitInterval)
    (a : PuncturedRaw X ι) :
    quotientRadial f t (puncturedQuotient f a) =
      puncturedQuotient f (Sum.map id (Sigma.map id (fun _ => radialDeformation t)) a) := by
  cases a with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i,z⟩
    change quotientMap f (if h : (z.1 : ℂ) ≠ 0 then _ else _) = _
    rw [dite_eq_left z.property]
    rfl
lemma quotientRadial_mem_neighborhood (f : ι → C(Circle, X)) (t : unitInterval)
    (y : puncturedNeighborhood f) : quotientRadial f t y ∈ puncturedNeighborhood f := by
  obtain ⟨a,ha⟩ := (puncturedQuotient_isQuotientMap f).surjective y
  rw [← ha, quotientRadial_puncturedQuotient]
  exact (puncturedQuotient f _).property
/-- The descended radial deformation, with codomain the genuine neighborhood. -/
def neighborhoodRadial (f : ι → C(Circle, X)) (t : unitInterval)
    (y : puncturedNeighborhood f) : puncturedNeighborhood f :=
  ⟨quotientRadial f t y, quotientRadial_mem_neighborhood f t y⟩
lemma neighborhoodRadial_puncturedQuotient (f : ι → C(Circle, X)) (t : unitInterval)
    (a : PuncturedRaw X ι) :
    neighborhoodRadial f t (puncturedQuotient f a) =
      puncturedQuotient f (Sum.map id (Sigma.map id (fun _ => radialDeformation t)) a) := by
  apply Subtype.ext
  exact quotientRadial_puncturedQuotient f t a
/-- The raw deformation is jointly continuous, using the coproduct and sigma topologies. -/
lemma puncturedQuotient_radial_continuous (f : ι → C(Circle, X)) :
    Continuous (fun p : unitInterval × PuncturedRaw X ι =>
      puncturedQuotient f (Sum.map id (Sigma.map id (fun _ => radialDeformation p.1)) p.2)) := by
  have hl : Continuous (fun p : unitInterval × X => puncturedQuotient f (.inl p.2)) :=
    (puncturedQuotient f).continuous.comp (continuous_inl.comp continuous_snd)
  have hs : Continuous (fun p : Σ _ : ι, PuncturedDisk × unitInterval =>
      puncturedQuotient f (.inr ⟨p.1, radialDeformation p.2.2 p.2.1⟩)) := by
    apply continuous_sigma
    intro i
    exact (puncturedQuotient f).continuous.comp
      (continuous_inr.comp (continuous_sigmaMk.comp
        (radialDeformation_continuous.comp continuous_swap)))
  let e : unitInterval × (Σ _ : ι, PuncturedDisk) ≃ₜ
      (Σ _ : ι, PuncturedDisk × unitInterval) :=
    (Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib
  have hr : Continuous (fun p : unitInterval × (Σ _ : ι, PuncturedDisk) =>
      puncturedQuotient f (.inr ⟨p.2.1, radialDeformation p.1 p.2.2⟩)) :=
    hs.comp e.continuous
  convert (hl.sumElim hr).comp (Homeomorph.prodSumDistrib.continuous) using 1
  ext p
  rcases p with ⟨t,a⟩
  cases a <;> rfl
/-- Joint continuity of the quotient homotopy, rather than continuity at each time. -/
lemma neighborhoodRadial_continuous (f : ι → C(Circle, X)) :
    Continuous (fun p : unitInterval × puncturedNeighborhood f => neighborhoodRadial f p.1 p.2) := by
  apply (puncturedQuotient_isQuotientMap f).continuous_lift_prod_right
  simpa only [neighborhoodRadial_puncturedQuotient] using puncturedQuotient_radial_continuous f
@[simp] lemma neighborhoodRadial_zero (f : ι → C(Circle, X))
    (y : puncturedNeighborhood f) : neighborhoodRadial f 0 y = y := by
  obtain ⟨a,rfl⟩ := (puncturedQuotient_isQuotientMap f).surjective y
  rw [neighborhoodRadial_puncturedQuotient]
  congr 1
  cases a with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i,z⟩
    change (Sum.inr ⟨i, radialDeformation 0 z⟩ : PuncturedRaw X ι) = Sum.inr ⟨i,z⟩
    rw [radialDeformation_zero]
lemma neighborhoodRadial_one (f : ι → C(Circle, X)) (x₀ : X)
    (y : puncturedNeighborhood f) :
    neighborhoodRadial f 1 y = neighborhoodInclusion f (neighborhoodRetraction f x₀ y) := by
  obtain ⟨a,rfl⟩ := (puncturedQuotient_isQuotientMap f).surjective y
  apply Subtype.ext
  cases a with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i,z⟩
    change quotientRadial f 1 (puncturedQuotient f (.inr ⟨i,z⟩)) =
      inclusion f (quotientRetraction f x₀ (puncturedQuotient f (.inr ⟨i,z⟩)))
    rw [quotientRadial_puncturedQuotient]
    change characteristic f i (radialDeformation 1 z).1 =
      inclusion f (quotientRetraction f x₀ (puncturedQuotient f (.inr ⟨i,z⟩)))
    rw [quotientRetraction_puncturedQuotient]
    have h : (radialDeformation 1 z).1 = boundaryInclusion (polar z) :=
      Subtype.ext (radialDeformation_one_coordinate z)
    rw [h, characteristic_boundary]
    rfl
/-- A proved deformation homotopy from the neighborhood identity to inclusion∘retraction. -/
def neighborhoodDeformation (f : ι → C(Circle, X)) (x₀ : X) :
    ContinuousMap.Homotopy (ContinuousMap.id (puncturedNeighborhood f))
      ((neighborhoodInclusion f).comp (neighborhoodRetraction f x₀)) where
  toFun p := neighborhoodRadial f p.1 p.2
  continuous_toFun := neighborhoodRadial_continuous f
  map_zero_left := neighborhoodRadial_zero f
  map_one_left := neighborhoodRadial_one f x₀
/-- The original space is genuinely homotopy equivalent to the punctured neighborhood. -/
def neighborhoodHomotopyEquiv (f : ι → C(Circle, X)) (x₀ : X) :
    ContinuousMap.HomotopyEquiv X (puncturedNeighborhood f) where
  toFun := neighborhoodInclusion f
  invFun := neighborhoodRetraction f x₀
  left_inv := by
    have h : (neighborhoodRetraction f x₀).comp (neighborhoodInclusion f) =
        ContinuousMap.id X := by ext x; rfl
    rw [h]
  right_inv := ⟨(neighborhoodDeformation f x₀).symm⟩
end CellAttachment
end
end CellAttachment_Deformation
/-! Source module: CellAttachment.HomotopyPi1 -/
section CellAttachment_HomotopyPi1
/-! # Compatible fundamental-group maps induced by actual homotopy equivalences -/
noncomputable section
namespace CellAttachment
universe u v
open CategoryTheory
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
/-- The actual fundamental-group map of a homotopy equivalence is bijective. -/
theorem homotopyEquivPi1_bijective (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Function.Bijective (FundamentalGroup.map e.toFun x) :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.map_bijective
    (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk x)
/-- A compatible pi1 equivalence whose underlying map is the actual induced map. -/
def homotopyEquivPi1 (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  MulEquiv.ofBijective (FundamentalGroup.map e.toFun x) (homotopyEquivPi1_bijective e x)
@[simp] theorem homotopyEquivPi1_apply (e : ContinuousMap.HomotopyEquiv X Y) (x : X)
    (g : FundamentalGroup X x) : homotopyEquivPi1 e x g = FundamentalGroup.map e.toFun x g := rfl
end CellAttachment
end
end CellAttachment_HomotopyPi1
/-! Source module: CellAttachment.NeighborhoodPi1 -/
section CellAttachment_NeighborhoodPi1
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
end
end CellAttachment_NeighborhoodPi1
/-! Source module: CellAttachment.GeometricPushout -/
section CellAttachment_GeometricPushout
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
end
end CellAttachment_GeometricPushout
/-! Source module: CellAttachment.Statement -/
section CellAttachment_Statement
/-!
# Exact target: attaching any family of two-cells
This module fixes the theorem statement before the geometric proof is assembled.
It contains definitions and no asserted or admitted cell-attachment theorem.
-/
noncomputable section
namespace CellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
/-- The actual attaching loop in X, whiskered chronologically from the basepoint
along a chosen path, around the attaching circle once, and back. -/
def attachingLoop (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) (i : ι) : Path x₀ x₀ :=
  (γ i).trans ((circleGenerator.map (f i).continuous).trans (γ i).symm)
/-- Its class in Mathlib's ordinary continuous-path fundamental group. -/
def attachingLoopClass (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) : ι → FundamentalGroup X x₀ :=
  fun i => .mk (attachingLoop f x₀ γ i)
/-- Precisely the normal subgroup generated by the chosen conjugated attaching loops. -/
def attachingNormalClosure (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) : Subgroup (FundamentalGroup X x₀) :=
  Subgroup.normalClosure (Set.range (attachingLoopClass f x₀ γ))
instance attachingNormalClosure_normal (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) : (attachingNormalClosure f x₀ γ).Normal := by
  unfold attachingNormalClosure
  infer_instance
/-- The full arbitrary-family two-cell attachment theorem, including compatibility
of the quotient equivalence with the actual inclusion-induced map. The index
universe and the space universe are independent. -/
def completeStatement : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] {ι : Type v}
    (f : ι → C(Circle, X)) (x₀ : X) (γ : ∀ i, Path x₀ (f i 1)),
    Function.Surjective (inclusionPi1 f x₀) ∧
    (inclusionPi1 f x₀).ker = attachingNormalClosure f x₀ γ ∧
    ∃ e : FundamentalGroup X x₀ ⧸ attachingNormalClosure f x₀ γ ≃*
      FundamentalGroup (Space f) (inclusion f x₀),
      e.toMonoidHom.comp (QuotientGroup.mk' (attachingNormalClosure f x₀ γ)) =
        inclusionPi1 f x₀
end CellAttachment
end
end CellAttachment_Statement
/-! Source module: CellAttachment.RelatorTransport -/
section CellAttachment_RelatorTransport
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
end
end CellAttachment_RelatorTransport
/-! Source module: CellAttachment.EquivalenceExactness -/
section CellAttachment_EquivalenceExactness
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
end CellAttachment_EquivalenceExactness
/-! Source module: CellAttachment.Main -/
section CellAttachment_Main
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
end
end CellAttachment_Main
