module

public import ArtinMatthews.SourceKPFiniteTranslateFibers
public import ArtinMatthews.SourceKPCompactRationalTransport


set_option backward.privateInPublic true
@[expose] public section

/-! The actual common-level rational quotient in upper-half-space coordinates. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "F" => SourceKPFiniteLevelFiber K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "A" => SourceKPArchUpperHalfSpace K
local notation "Γ" => PGL(2, K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ

variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ T

instance sourceKPTranslateFiniteLevelFiber_topology : TopologicalSpace FJ := ⊥
instance sourceKPTranslateFiniteLevelFiber_discrete : DiscreteTopology FJ := ⟨rfl⟩

abbrev SourceKPTranslateUpperSpace := A × FJ

local notation "XJ" => SourceKPTranslateUpperSpace K hζ T

instance sourceKPTranslateUpper_rationalAction : MulAction Γ XJ where
  smul γ x := (sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ γ) x.1,
    sourceKPRationalFiniteMap K hζ γ • x.2)
  one_smul x := by
    apply Prod.ext
    · change sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ 1) x.1 = x.1
      rw [map_one, sourceKPArchUpperAction_one]
    · change sourceKPRationalFiniteMap K hζ 1 • x.2 = x.2
      rw [map_one, one_smul]
  mul_smul γ δ x := by
    apply Prod.ext
    · change sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ (γ * δ)) x.1 =
        sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ γ)
          (sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ δ) x.1)
      rw [map_mul, sourceKPArchUpperAction_mul]
    · change sourceKPRationalFiniteMap K hζ (γ * δ) • x.2 =
        sourceKPRationalFiniteMap K hζ γ • (sourceKPRationalFiniteMap K hζ δ • x.2)
      rw [map_mul, mul_smul]

instance sourceKPTranslateUpper_rationalContinuous : ContinuousConstSMul Γ XJ where
  continuous_const_smul γ := by
    change Continuous (fun x : XJ =>
      (sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ γ) x.1,
        sourceKPRationalFiniteMap K hζ γ • x.2))
    exact ((sourceKPArchUpperAction_continuous K hζ (sourceKPRationalArchMap K hζ γ)).comp
      continuous_fst).prodMk
      ((continuous_of_discreteTopology : Continuous (fun b : FJ =>
        sourceKPRationalFiniteMap K hζ γ • b)).comp continuous_snd)

def SourceKPTranslateAutomorphicCompactLevel :=
  Quotient (MulAction.orbitRel Γ XJ)

local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T

instance sourceKPTranslateAutomorphicCompactLevel_topology : TopologicalSpace YJ :=
  inferInstanceAs (TopologicalSpace (Quotient (MulAction.orbitRel Γ XJ)))

instance sourceKPTranslateAutomorphicCompactLevel_measurable : MeasurableSpace YJ := borel _
instance sourceKPTranslateAutomorphicCompactLevel_borel : BorelSpace YJ := ⟨rfl⟩

def sourceKPTranslateUpperMk (x : XJ) : YJ := Quotient.mk _ x

theorem sourceKPTranslateUpperMk_isOpenQuotientMap :
    IsOpenQuotientMap (sourceKPTranslateUpperMk K hζ T) :=
  MulAction.isOpenQuotientMap_quotientMk

def sourceKPTranslateAutomorphicCompactMk (a : PGL(2, InfiniteAdeleRing K)) (b : Gf) : YJ :=
  sourceKPTranslateUpperMk K hζ T
    (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a), QuotientGroup.mk b)

def sourceKPTranslateAutomorphicCompactMap (t : Gf) (h : J ≤ D t) : YJ → Y :=
  Quotient.lift (fun x : XJ =>
    sourceKPUpperToCompact K hζ (sourceKPFiniteRightTranslateMap K hζ T t h x.2) x.1) (by
      intro x y hxy
      obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp hxy
      rw [← hγ]
      change sourceKPUpperToCompact K hζ
        (sourceKPFiniteRightTranslateMap K hζ T t h (sourceKPRationalFiniteMap K hζ γ • y.2))
        (sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ γ) y.1) = _
      rw [sourceKPFiniteRightTranslateMap_smul]
      exact sourceKPUpperToCompact_rational K hζ γ
        (sourceKPFiniteRightTranslateMap K hζ T t h y.2) y.1)

theorem sourceKPTranslateAutomorphicCompactMap_upperMk (t : Gf) (h : J ≤ D t) (x : XJ) :
    sourceKPTranslateAutomorphicCompactMap K hζ T t h (sourceKPTranslateUpperMk K hζ T x) =
      sourceKPUpperToCompact K hζ (sourceKPFiniteRightTranslateMap K hζ T t h x.2) x.1 :=
  rfl

theorem sourceKPTranslateAutomorphicCompactMap_mk (t : Gf) (h : J ≤ D t)
    (a : PGL(2, InfiniteAdeleRing K)) (b : Gf) :
    sourceKPTranslateAutomorphicCompactMap K hζ T t h
      (sourceKPTranslateAutomorphicCompactMk K hζ T a b) =
        sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ (a,b * t)) := by
  rw [sourceKPTranslateAutomorphicCompactMk, sourceKPTranslateAutomorphicCompactMap_upperMk]
  change sourceKPUpperToCompact K hζ (sourceKPFiniteRightTranslateMap K hζ T t h (QuotientGroup.mk b))
    (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a)) = _
  rw [sourceKPFiniteRightTranslateMap_mk]
  exact sourceKPUpperToCompact_mk K hζ (QuotientGroup.mk (b * t) : F) a

theorem sourceKPTranslateAutomorphicCompactMap_continuous (t : Gf) (h : J ≤ D t) :
    Continuous (sourceKPTranslateAutomorphicCompactMap K hζ T t h) := by
  have hc : Continuous (fun x : XJ =>
      sourceKPUpperToCompact K hζ (sourceKPFiniteRightTranslateMap K hζ T t h x.2) x.1) := by
    apply continuous_prod_of_discrete_right.mpr
    intro b
    exact sourceKPUpperToCompact_continuous K hζ (sourceKPFiniteRightTranslateMap K hζ T t h b)
  exact hc.quotient_lift _

theorem sourceKPTranslateAutomorphicCompactMap_surjective (t : Gf) (h : J ≤ D t) :
    Function.Surjective (sourceKPTranslateAutomorphicCompactMap K hζ T t h) := by
  intro y
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  obtain ⟨c,hc⟩ := sourceKPFiniteRightTranslateMap_surjective K hζ T t h b
  refine ⟨sourceKPTranslateUpperMk K hζ T (p,c), ?_⟩
  rw [sourceKPTranslateAutomorphicCompactMap_upperMk]
  exact congrArg (fun v => sourceKPUpperToCompact K hζ v p) hc

theorem sourceKPTranslateAutomorphicCompactMap_finite_fiber (t : Gf) (h : J ≤ D t) (y : Y) :
    Set.Finite ((sourceKPTranslateAutomorphicCompactMap K hζ T t h) ⁻¹' {y}) := by
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  let L := {c : FJ // sourceKPFiniteRightTranslateMap K hζ T t h c = b}
  let : Finite L := sourceKPFiniteRightTranslateFiber_finite K hζ T t h b
  let f : L → YJ := fun c => sourceKPTranslateUpperMk K hζ T (p,c.val)
  apply (Set.finite_range f).subset
  intro x hx
  induction x using Quotient.inductionOn with
  | _ u =>
    change sourceKPUpperToCompact K hζ (sourceKPFiniteRightTranslateMap K hζ T t h u.2) u.1 =
      sourceKPUpperToCompact K hζ b p at hx
    obtain ⟨γ,hfin,harch⟩ :=
      (sourceKPUpperToCompact_eq_iff_rational K hζ b _ p u.1).mp hx.symm
    let c : FJ := sourceKPRationalFiniteMap K hζ γ • u.2
    have hc : sourceKPFiniteRightTranslateMap K hζ T t h c = b := by
      unfold c
      rw [sourceKPFiniteRightTranslateMap_smul]
      exact hfin
    refine ⟨⟨c,hc⟩,?_⟩
    apply Quotient.sound
    exact MulAction.mem_orbit_iff.mpr ⟨γ,Prod.ext harch rfl⟩

end
end ArtinMatthews
