module

public import ArtinMatthews.SourceKPLocalCompactSeedOrbit
public import ArtinMatthews.SourceKPLocalCompactGlobalLevel
public import ArtinMatthews.SourceKPLocalCompactFlatTorus
public import ArtinMatthews.SourceKPLocalCompactCosets
public import ArtinMatthews.SourceKPLocalCompactFlatBorel
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
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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

/-! At a fixed retained finite place and fixed base-one adelic remainder,
the actual compact section has a common finite carrier for every spectral
parameter. It is generated at parameter zero using the genuine deep
compact cosets and local cube classes. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "Gₐ" => SourceKPAdelicProjective K hζ
local notation "B" => SourceFiniteKPProjectiveBorel K hζ P
local notation "C" => sourceKPLocalCompactCover K hζ P
local notation "J" => sourceKPLocalCompactDeep K hζ P
local notation "Q" => SourceKPLocalCompactCubeClasses K P
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "ρ" => sourceKPAdelicLocalBorelRepresentation K hζ P
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P
local notation "F" => sourceKPAdelicCompactSection K hζ
local notation "E" => sourceKPLocalCompactTorusFlatEquiv K hζ

local instance sourceKPLocalCompactRetainedAmbientAddCommGroup (s : ℂ) :
    AddCommGroup (V s) := Submodule.addCommGroup _

def sourceKPLocalCompactRestrictedSection (r : Gₐ)
    (hr : sourceKPAdelicLocalBase K hζ P r = 1) (s : ℂ) :
    sourceKPLocalCompactFixedSpace K hζ P (ρ s) := by
  let f : G → V s := fun g => (F s).val (ι₀ g*r)
  have hcov (b : B) (g : G) : f (b.val*g) = ρ s b (f g) := by
    have he : ι₀ (b.val*g)*r = ι₀ b.val*(ι₀ g*r) := by
      rw [map_mul ι₀,mul_assoc]
    exact (congrArg (F s).val he).trans
      ((F s).property (sourceKPAdelicLocalBorel K hζ P b) (ι₀ g*r))
  exact ⟨⟨f,hcov⟩,fun g j => sourceKPLocalCompactGlobalSection_deep_right K hζ P s r hr g j⟩

theorem sourceKPLocalCompactRestrictedSection_apply (r : Gₐ)
    (hr : sourceKPAdelicLocalBase K hζ P r = 1) (s : ℂ) (g : G) :
    (sourceKPLocalCompactRestrictedSection K hζ P r hr s).val.val g =
      (F s).val (ι₀ g*r) := rfl

def sourceKPLocalCompactRetainedCarrier (r : Gₐ)
    (hr : sourceKPAdelicLocalBase K hζ P r = 1) : Submodule ℂ (V 0) :=
  sourceKPLocalCompactSeedOrbit K hζ P 0
    (sourceKPLocalCompactRestriction K hζ P (ρ 0)
      (sourceKPLocalCompactRestrictedSection K hζ P r hr 0))

local notation "W" => sourceKPLocalCompactRetainedCarrier K hζ P
local notation "base" => sourceKPAdelicLocalBase K hζ P

theorem sourceKPLocalCompactRetainedCarrier_finiteDimensional (r : Gₐ) (hr : base r = 1) :
    FiniteDimensional ℂ (W r hr) := by
  let : Finite (C ⧸ J) := sourceKPLocalCompactCosets_finite K hζ P
  exact sourceKPLocalCompactSeedOrbit_finiteDimensional K hζ P 0 _

theorem sourceKPLocalCompactRetainedCarrier_finrank_le (r : Gₐ) (hr : base r = 1) :
    Module.finrank ℂ (W r hr) ≤ Nat.card Q * Nat.card (C ⧸ J) := by
  let : Finite (C ⧸ J) := sourceKPLocalCompactCosets_finite K hζ P
  exact sourceKPLocalCompactSeedOrbit_finrank_le K hζ P 0 _

theorem sourceKPLocalCompactRetainedValue_mem (r : Gₐ) (hr : base r = 1) (s : ℂ) (g : G) :
    (E s).symm ((F s).val (ι₀ g*r)) ∈ (W r hr) := by
  have hz : (F 0).val (ι₀ g*r) ∈ (W r hr) :=
    sourceKPLocalCompactSeedOrbit_induced_mem K hζ P 0
      (sourceKPLocalCompactRestrictedSection K hζ P r hr 0) g
  obtain ⟨a,ha⟩ := sourceKPLocalCompactSection_flat K hζ s (ι₀ g*r)
  have he : (E s).symm ((F s).val (ι₀ g*r)) = (a : ℂ) • (F 0).val (ι₀ g*r) := by
    rw [ha]
    exact ((E s).symm.toLinearMap.map_smul (a : ℂ) _).trans
      (congrArg (fun v : V 0 => (a : ℂ) • v) ((E s).symm_apply_apply _))
  rw [he]
  exact (W r hr).smul_mem (a : ℂ) hz

def sourceKPLocalCompactRetainedRestriction (r : Gₐ) (hr : base r = 1) (s : ℂ) (q : C ⧸ J) : (W r hr) :=
  ⟨(E s).symm ((F s).val (ι₀ q.out.val*r)),
    sourceKPLocalCompactRetainedValue_mem K hζ P r hr s q.out.val⟩

theorem sourceKPLocalCompactRetainedRestriction_apply (r : Gₐ) (hr : base r = 1) (s : ℂ) (k : C) :
    (sourceKPLocalCompactRetainedRestriction K hζ P r hr s (QuotientGroup.mk k)).val =
      (E s).symm ((F s).val (ι₀ k.val*r)) := by
  obtain ⟨j,hj⟩ := QuotientGroup.mk_out_eq_mul (s := J) k
  change (E s).symm ((F s).val (ι₀ ((QuotientGroup.mk k : C ⧸ J).out.val)*r)) = _
  rw [hj]
  exact congrArg (E s).symm
    (sourceKPLocalCompactGlobalSection_deep_right K hζ P s r hr k.val j)

theorem sourceKPLocalCompactRetainedRestriction_covariant (r : Gₐ) (hr : base r = 1) (s : ℂ) (b : B)
    (hb : b.val ∈ C) (k : C) :
    (sourceKPLocalCompactRetainedRestriction K hζ P r hr s
      (QuotientGroup.mk ((⟨b.val,hb⟩ : C)*k))).val =
      ρ 0 b (sourceKPLocalCompactRetainedRestriction K hζ P r hr s (QuotientGroup.mk k)).val := by
  rw [sourceKPLocalCompactRetainedRestriction_apply K hζ P r hr,
    sourceKPLocalCompactRetainedRestriction_apply K hζ P r hr]
  apply (E s).injective
  rw [(E s).apply_symm_apply, ← sourceKPLocalCompactBorelFlat_action K hζ P s b hb,
    (E s).apply_symm_apply]
  change (F s).val (ι₀ (b.val*k.val)*r) = ρ s b ((F s).val (ι₀ k.val*r))
  rw [map_mul ι₀,mul_assoc]
  exact sourceAlgebraicInducedSpace_covariant _ _ (F s)
    (sourceKPAdelicLocalBorel K hζ P b) (ι₀ k.val*r)

theorem sourceKPLocalCompactRetainedRestriction_finiteDimensional (r : Gₐ) (hr : base r = 1) :
    FiniteDimensional ℂ ((C ⧸ J) → (W r hr)) := by
  let : Finite (C ⧸ J) := sourceKPLocalCompactCosets_finite K hζ P
  let : FiniteDimensional ℂ (W r hr) := sourceKPLocalCompactRetainedCarrier_finiteDimensional K hζ P r hr
  infer_instance

end
end ArtinMatthews
