import CellAttachment.GroupQuotient
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Vertex-group tools for a categorical van Kampen square

These are abstract groupoid lemmas. They do not assert that a particular cell-attachment
space has the required open cover, connectivity, or disk and annulus homotopy types.
-/

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
    simp
  · ext x
    have he : Arrow.mk (d.obj (l.obj x)).hom = Arrow.mk (b.app x) := by
      rw [Arrow.mk_eq]
      exact Functor.congr_obj hdl x
    obtain ⟨hx, hy, hh⟩ := (Arrow.mk_eq_mk_iff _ _).mp he
    dsimp [t]
    simp only [eqToHom_app, Arrow.leftToRight_app]
    rw [hh]
    simp

end ArrowDescent

end CellAttachment
