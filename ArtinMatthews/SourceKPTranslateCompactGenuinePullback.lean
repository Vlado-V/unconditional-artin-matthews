module

public import ArtinMatthews.SourceKPTranslateCompactL2
public import ArtinMatthews.SourceKPCompactGenuineL2
public import ArtinMatthews.SourceKPTranslateCompactCenter
public import ArtinMatthews.SourceKPTranslateCompactHaarCenter
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine Haar L² retains its forward cubic character on the actual common level. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "Z" => rootsOfUnity 3 K
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T
local notation "μJ" => sourceKPTranslateCompactHaar K hζ T

theorem sourceKPTranslateCompactPullbackL2_genuine (t : Gf) (h : J ≤ D t)
    (f : SourceKPGenuineAutomorphicL2 K hζ) (z : Z) :
    (fun x : YJ => sourceKPTranslateCompactPullbackL2 K hζ T t h f.val (z • x)) =ᵐ[μJ]
      fun x => (sourceKPAdelicCentralComplex K hζ z : ℂ) *
        sourceKPTranslateCompactPullbackL2 K hζ T t h f.val x := by
  let p := sourceKPTranslateAutomorphicCompactMap K hζ T t h
  let F := sourceKPTranslateCompactPullbackL2 K hζ T t h f.val
  have hf := ((sourceKPCompactGenuineL2Subspace_mem_ae K hζ (sourceKPArchHaar K hζ)
    f.val).mp f.prop) z
  have hcoe := sourceKPTranslateCompactPullbackL2_coe K hζ T t h f.val
  have hm := sourceKPTranslateCompactHaar_center_preserving K hζ T z
  have hshift := hm.quasiMeasurePreserving.ae_eq_comp hcoe
  have hχ := (sourceKPTranslateAutomorphicCompactMap_quasiMeasurePreserving K hζ T t h).ae_eq_comp hf
  change ∀ᵐ x ∂μJ, F (z • x) = f.val (p (z • x)) at hshift
  change ∀ᵐ x ∂μJ, f.val (z • p x) =
    (sourceKPAdelicCentralComplex K hζ z : ℂ) * f.val (p x) at hχ
  filter_upwards [hcoe, hshift, hχ] with x hFx hFzx hx
  have hp : p (z • x) = z • p x :=
    sourceKPTranslateAutomorphicCompactMap_center K hζ T t h z x
  change F x = f.val (p x) at hFx
  change F (z • x) = (sourceKPAdelicCentralComplex K hζ z : ℂ) * F x
  rw [hFzx, hp, hx, hFx]

end
end ArtinMatthews
