module

public import ArtinMatthews.SourceKPIntegralResiduePhase
public import ArtinMatthews.SourceKPTameSpherical
public import ArtinMatthews.StandardLocalConductor
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

/-! Stable Jacquet integration on the actual induced space. The domain
records genuine eventual integrability and stabilization. Linearity
uses the stabilized values on a common sufficiently large ball. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical AllowedGenerators Filter
open scoped NumberField SourcePhysical MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "B" => sourceLocalBall K P.val
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val

abbrev sourceKPTameExteriorInducedSpace := sourceKPTameInducedSpace K hζ P.val h₆ π₀ hπ₀

abbrev sourceKPTameExteriorInducedRepresentation :=
  sourceKPTameInducedRepresentation K hζ P.val h₆ π₀ hπ₀

local notation "I₀" => sourceKPTameExteriorInducedSpace K hζ S₀ P

def sourceKPTameJacquetInducedIntegrand (f : I₀) (x : L) : ZMod 3 → ℂ :=
  localFiniteCharacter K P.val (-x) • f.val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))

def sourceKPTameJacquetInducedTruncation (f : I₀) (N : ℕ) : ZMod 3 → ℂ :=
  ∫ x in B (N : ℤ), sourceKPTameJacquetInducedIntegrand K hζ S₀ P f x ∂μ₀

def sourceKPTameJacquetHasStableValue (f : I₀) (j : ZMod 3 → ℂ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    IntegrableOn (sourceKPTameJacquetInducedIntegrand K hζ S₀ P f) (B (N : ℤ)) μ₀ ∧
      sourceKPTameJacquetInducedTruncation K hζ S₀ P f N = j

theorem sourceKPTameJacquetHasStableValue_unique {f : I₀} {j j' : ZMod 3 → ℂ}
    (h : sourceKPTameJacquetHasStableValue K hζ S₀ P f j)
    (h' : sourceKPTameJacquetHasStableValue K hζ S₀ P f j') : j = j' := by
  obtain ⟨_, hN, h'N⟩ := (h.and h').exists
  exact hN.2.symm.trans h'N.2

theorem sourceKPTameJacquetHasStableValue_zero :
    sourceKPTameJacquetHasStableValue K hζ S₀ P (0 : I₀) 0 := by
  have h : sourceKPTameJacquetInducedIntegrand K hζ S₀ P (0 : I₀) = 0 := by
    funext x
    change localFiniteCharacter K P.val (-x) • (0 : ZMod 3 → ℂ) = 0
    exact smul_zero _
  exact Eventually.of_forall (fun N => by
    rw [sourceKPTameJacquetInducedTruncation, h]
    exact ⟨integrableOn_zero, integral_zero L (ZMod 3 → ℂ)⟩)

theorem sourceKPTameJacquetHasStableValue_add {f g : I₀} {j k : ZMod 3 → ℂ}
    (hf : sourceKPTameJacquetHasStableValue K hζ S₀ P f j)
    (hg : sourceKPTameJacquetHasStableValue K hζ S₀ P g k) :
    sourceKPTameJacquetHasStableValue K hζ S₀ P (f + g) (j + k) := by
  have h : sourceKPTameJacquetInducedIntegrand K hζ S₀ P (f + g) =
      fun x => sourceKPTameJacquetInducedIntegrand K hζ S₀ P f x +
        sourceKPTameJacquetInducedIntegrand K hζ S₀ P g x := by
    funext x
    exact smul_add _ _ _
  filter_upwards [hf, hg] with N hF hG
  refine ⟨?_, ?_⟩
  · rw [h]
    exact hF.1.add hG.1
  · calc
      _ = sourceKPTameJacquetInducedTruncation K hζ S₀ P f N +
          sourceKPTameJacquetInducedTruncation K hζ S₀ P g N := by
        unfold sourceKPTameJacquetInducedTruncation
        rw [h, integral_add hF.1 hG.1]
      _ = _ := congrArg₂ (· + ·) hF.2 hG.2

theorem sourceKPTameJacquetHasStableValue_smul (c : ℂ) {f : I₀} {j : ZMod 3 → ℂ}
    (hf : sourceKPTameJacquetHasStableValue K hζ S₀ P f j) :
    sourceKPTameJacquetHasStableValue K hζ S₀ P (c • f) (c • j) := by
  have h : sourceKPTameJacquetInducedIntegrand K hζ S₀ P (c • f) =
      fun x => c • sourceKPTameJacquetInducedIntegrand K hζ S₀ P f x := by
    funext x
    exact smul_comm (localFiniteCharacter K P.val (-x)) c
      (f.val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)))
  filter_upwards [hf] with N hF
  refine ⟨?_, ?_⟩
  · rw [h]
    exact hF.1.smul c
  · calc
      _ = c • sourceKPTameJacquetInducedTruncation K hζ S₀ P f N := by
        unfold sourceKPTameJacquetInducedTruncation
        rw [h, integral_smul]
      _ = _ := congrArg (c • ·) hF.2

def sourceKPTameJacquetStableSpace : Submodule ℂ I₀ where
  carrier := {f | ∃ j, sourceKPTameJacquetHasStableValue K hζ S₀ P f j}
  zero_mem' := ⟨0, sourceKPTameJacquetHasStableValue_zero K hζ S₀ P⟩
  add_mem' := fun ⟨j, hj⟩ ⟨k, hk⟩ => ⟨j + k, sourceKPTameJacquetHasStableValue_add K hζ S₀ P hj hk⟩
  smul_mem' := fun c _ ⟨j, hj⟩ => ⟨c • j, sourceKPTameJacquetHasStableValue_smul K hζ S₀ P c hj⟩

def sourceKPTameJacquetStableMap : sourceKPTameJacquetStableSpace K hζ S₀ P →ₗ[ℂ] (ZMod 3 → ℂ) where
  toFun f := f.property.choose
  map_add' f g := sourceKPTameJacquetHasStableValue_unique K hζ S₀ P (f + g).property.choose_spec
    (sourceKPTameJacquetHasStableValue_add K hζ S₀ P f.property.choose_spec g.property.choose_spec)
  map_smul' c f := sourceKPTameJacquetHasStableValue_unique K hζ S₀ P (c • f).property.choose_spec
    (sourceKPTameJacquetHasStableValue_smul K hζ S₀ P c f.property.choose_spec)

theorem sourceKPTameJacquetStableMap_hasStableValue (f : sourceKPTameJacquetStableSpace K hζ S₀ P) :
    sourceKPTameJacquetHasStableValue K hζ S₀ P f.val (sourceKPTameJacquetStableMap K hζ S₀ P f) :=
  f.property.choose_spec

end
end ArtinMatthews
