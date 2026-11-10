module

public import ArtinMatthews.SourceReflectionSUnitCharacter
public import ArtinMatthews.SourceKPRetainedTinySixth
public import ArtinMatthews.StandardLocalBall
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

/-! The actual row phase is locally constant at one and continuous on the whole S-local group. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain Filter SourcePhysical
open scoped NumberField Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => sourceHilbertSet K S₀
local notation "U" => SWholeUnits K S
local notation "X" => exteriorUnitSubgroup S

theorem sourceReflectionSUnitCharacter_continuous (u : X) :
    Continuous (sourceReflectionSUnitCharacter K hζ S₀ u) := by
  let χ := sourceReflectionSUnitCharacter K hζ S₀ u
  choose M hM hroot using fun v : S => sourceKPRetained_tiny_sixth K v.val
  have hn (v : S) : ∀ᶠ x : U in 𝓝 1,
      ((x.2 v : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)-1 ∈
        sourceLocalBall K v.val (-(M v : ℤ)) := by
    let f (x : U) : v.1.adicCompletion K := (x.2 v : v.1.adicCompletion K)-1
    have hc : Continuous f := (Units.continuous_val.comp
      ((continuous_apply v).comp continuous_snd)).sub continuous_const
    have hf : f 1 = 0 := sub_self 1
    have hzero : f 1 ∈ sourceLocalBall K v.val (-(M v : ℤ)) := by
      rw [hf]
      exact (sourceLocalOpenBall K v.val (-(M v : ℤ))).zero_mem
    exact hc.continuousAt ((sourceLocalBall_isOpen K v.val _).mem_nhds hzero)
  apply continuous_of_tendsto_nhds_one χ
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_all.mpr hn] with x hx
  choose z hz using fun v => hroot v (x.2 v) (hx v)
  have he : x.2 = (1 : U).2 * z^6 := by
    funext v
    change x.2 v = 1 * z v ^ 6
    rw [one_mul, hz v]
  exact ((sourceReflectionSUnitCharacter_eq_of_finite_sixth_mul K hζ S₀ u z he).trans
    (map_one χ)).symm

theorem sourceReflectionSUnitCharacter_val_measurable [MeasurableSpace U] [BorelSpace U]
    (u : X) : Measurable (fun x : U => (sourceReflectionSUnitCharacter K hζ S₀ u x : ℂ)) :=
  (Units.continuous_val.comp (sourceReflectionSUnitCharacter_continuous K hζ S₀ u)).measurable

theorem sourceReflectionSUnitCharacter_measurable [MeasurableSpace U] [BorelSpace U]
    (u : X) : Measurable (sourceReflectionSUnitCharacter K hζ S₀ u) :=
  measurable_comap_iff.mpr (sourceReflectionSUnitCharacter_val_measurable K hζ S₀ u)

end
end ArtinMatthews.SourceEulerAssembly
