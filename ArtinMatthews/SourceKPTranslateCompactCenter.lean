module

public import ArtinMatthews.SourceKPTranslateCompactLevel
public import ArtinMatthews.SourceKPCubicUpperAction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual cubic center and its equivariance under the common-level maps. -/
namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "Γ" => PGL(2, K)
local notation "Z" => rootsOfUnity 3 K
local notation "c" => sourceKPFiniteAdeleProjectiveCenter K hζ

variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ T
local notation "XJ" => SourceKPTranslateUpperSpace K hζ T
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T

instance sourceKPTranslateUpper_centerAction : MulAction Z XJ where
  smul z x := (x.1, c z • x.2)
  one_smul x := Prod.ext rfl (by
    change c 1 • x.2 = x.2
    rw [map_one, one_smul])
  mul_smul z w x := Prod.ext rfl (by
    change c (z * w) • x.2 = c z • (c w • x.2)
    rw [map_mul, mul_smul])

instance sourceKPTranslateUpper_rationalCenterComm : SMulCommClass Γ Z XJ where
  smul_comm γ z x := Prod.ext rfl (by
    change sourceKPRationalFiniteMap K hζ γ • (c z • x.2) =
      c z • (sourceKPRationalFiniteMap K hζ γ • x.2)
    rw [smul_smul, smul_smul, (sourceKPFiniteAdeleProjectiveCenter_commute K hζ z
      (sourceKPRationalFiniteMap K hζ γ)).eq])

instance sourceKPTranslateUpper_centerContinuous : ContinuousSMul Z XJ where
  continuous_smul := by
    change Continuous (fun p : Z × XJ => (p.2.1, c p.1 • p.2.2))
    have h : Continuous (fun p : Z × FJ => c p.1 • p.2) := continuous_of_discreteTopology
    exact (continuous_fst.comp continuous_snd).prodMk
      (h.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

instance sourceKPTranslateCompact_centerAction : MulAction Z YJ :=
  sourceCommutingOrbitAction Γ Z XJ

instance sourceKPTranslateCompact_centerContinuous : ContinuousSMul Z YJ :=
  sourceCommutingOrbitAction_continuous Γ Z XJ

theorem sourceKPTranslateCompact_center_mk (z : Z) (a : PGL(2, InfiniteAdeleRing K)) (b : Gf) :
    z • sourceKPTranslateAutomorphicCompactMk K hζ T a b =
      sourceKPTranslateAutomorphicCompactMk K hζ T a (c z * b) :=
  rfl

theorem sourceKPTranslateAutomorphicCompactMap_center (t : Gf) (h : J ≤ D t)
    (z : Z) (x : YJ) :
    sourceKPTranslateAutomorphicCompactMap K hζ T t h (z • x) =
      z • sourceKPTranslateAutomorphicCompactMap K hζ T t h x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change sourceKPUpperToCompact K hζ
      (sourceKPFiniteRightTranslateMap K hζ T t h (c z • x.2)) x.1 =
        z • sourceKPUpperToCompact K hζ (sourceKPFiniteRightTranslateMap K hζ T t h x.2) x.1
    rw [sourceKPFiniteRightTranslateMap_smul, sourceKPCubicCenter_upperToCompact] <;> rfl

end
end ArtinMatthews
