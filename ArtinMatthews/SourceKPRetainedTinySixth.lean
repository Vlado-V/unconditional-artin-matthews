module

public import ArtinMatthews.StandardLocalConductor
public import ArtinMatthews.SourceKPJacquetTinyUnits
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

/-! A literal sufficiently deep principal-unit ball consists of sixth
powers in each retained completion, including the primes above two and three. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain SourcePhysical
open scoped NumberField SourcePhysical

noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "O" => P.adicCompletionIntegers K
local notation "B" => sourceLocalBall K P

theorem sourceKPRetained_tiny_sixth :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ t : Lˣ, ((t:L)-1) ∈ B (-(M:ℤ)) → ∃ w : Lˣ, w^6 = t := by
  obtain ⟨M,hM,hdeep⟩ := sourceKPJacquet_deep_ball_subset K P
  refine ⟨M,hM,fun t ht => ?_⟩
  obtain ⟨r,hr,he⟩ := hdeep ht
  change r ∈ sourceKPDeepIdeal K P at hr
  let x : O := 1+r
  have hx : x-1 ∈ sourceKPDeepIdeal K P := by simpa only [x,add_sub_cancel_left] using hr
  let h := sourceKPDeepEntry_isUnit K P x hx
  let u : Oˣ := h.unit
  have hu : (u:O) = x := h.unit_spec
  obtain ⟨w,hw⟩ := sixthLocal_exists_root P u (by rw [hu]; exact hx)
  let f : Oˣ →* Lˣ := Units.map (algebraMap O L).toMonoidHom
  refine ⟨f w,?_⟩
  rw [← map_pow, hw]
  apply Units.ext
  change algebraMap O L (u:O) = (t:L)
  rw [hu]
  dsimp only [x]
  rw [map_add,map_one,he]
  ring

end
end ArtinMatthews
