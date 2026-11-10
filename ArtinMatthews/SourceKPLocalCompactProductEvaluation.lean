module

public import ArtinMatthews.SourceKPLocalCompactProductLift
public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPLocalCompactCosets
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

/-! At a fixed exterior remainder the actual global section descends
simultaneously through the right deep cosets at every retained place. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

abbrev SourceKPLocalCompactProductCosets :=
  (P : S) → (sourceKPLocalCompactCover K hζ P.val ⧸ sourceKPLocalCompactDeep K hζ P.val)

local notation "G" => SourceKPAdelicProjective K hζ
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "D" => sourceKPAdelicDeepCompact K hζ
local notation "F" => sourceKPAdelicCompactSection K hζ
local notation "ρ" => sourceKPAdelicNormalizedBorelRepresentation K hζ
local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ S
local notation "Bₛ" => SourceKPLocalCompactProductBorel K hζ S
local notation "Cₛ" => SourceKPLocalCompactProductCompact K hζ S
local notation "Jₛ" => SourceKPLocalCompactProductDeep K hζ S
local notation "Qₛ" => SourceKPLocalCompactProductCosets K hζ S
local notation "L" => sourceKPLocalCompactProductLift K hζ S
local notation "Lᴮ" => sourceKPLocalCompactProductBorelLift K hζ S

theorem sourceKPLocalCompactProductCosets_finite : Finite Qₛ := by
  letI (P : S) : Finite (sourceKPLocalCompactCover K hζ P.val ⧸
      sourceKPLocalCompactDeep K hζ P.val) := sourceKPLocalCompactCosets_finite K hζ P.val
  exact inferInstanceAs (Finite ((P : S) → (sourceKPLocalCompactCover K hζ P.val ⧸
    sourceKPLocalCompactDeep K hζ P.val)))

theorem sourceKPLocalCompactProductCosets_card :
    Nat.card Qₛ = ∏ P : S, Nat.card
      (sourceKPLocalCompactCover K hζ P.val ⧸ sourceKPLocalCompactDeep K hζ P.val) :=
  Nat.card_pi

theorem sourceKPLocalCompactProductSection_deep_right (s : ℂ) (r : G)
    (hr : ∀ P : S, sourceKPAdelicLocalBase K hζ P.val r = 1) (g : Gₛ) (j : Jₛ) :
    (F s).val (L (g*(fun P => (j P).val.val))*r) = (F s).val (L g*r) := by
  let j₀ : Gₛ := fun P => (j P).val.val
  let k : D := ⟨L j₀,sourceKPLocalCompactProductDeep_mem K hζ S j⟩
  have hc := sourceKPLocalCompactProductLift_commute_of_base_one K hζ S j₀ r hr
  change (F s).val (L (g*j₀)*r) = _
  rw [map_mul L,mul_assoc,hc.eq,← mul_assoc]
  exact congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s => f.val (L g*r))
    (sourceKPAdelicCompactSection_right K hζ s k)

def sourceKPLocalCompactProductEvaluation (s : ℂ) (r : G) (q : Qₛ) : V s :=
  (F s).val (L (fun P => (q P).out.val)*r)

theorem sourceKPLocalCompactProductEvaluation_apply (s : ℂ) (r : G)
    (hr : ∀ P : S, sourceKPAdelicLocalBase K hζ P.val r = 1) (k : Cₛ) :
    sourceKPLocalCompactProductEvaluation K hζ S s r (fun P => QuotientGroup.mk (k P)) =
      (F s).val (L (fun P => (k P).val)*r) := by
  let q : Qₛ := fun P => QuotientGroup.mk (k P)
  choose j hj using fun P : S =>
    QuotientGroup.mk_out_eq_mul (s := sourceKPLocalCompactDeep K hζ P.val) (k P)
  have he : (fun P : S => (q P).out.val) =
      (fun P : S => (k P).val) * (fun P : S => (j P).val.val) := by
    funext P
    exact congrArg Subtype.val (hj P)
  change (F s).val (L (fun P => (q P).out.val)*r) = _
  rw [he]
  exact sourceKPLocalCompactProductSection_deep_right K hζ S s r hr
    (fun P => (k P).val) j

theorem sourceKPLocalCompactProductSection_borel (s : ℂ) (r : G) (b : Bₛ) (g : Gₛ) :
    (F s).val (L ((fun P => (b P).val)*g)*r) = ρ s (Lᴮ b) ((F s).val (L g*r)) := by
  rw [map_mul L,mul_assoc,← sourceKPLocalCompactProductBorelLift_val K hζ S b]
  exact (F s).property (Lᴮ b) (L g*r)

end
end ArtinMatthews
