module

public import ArtinMatthews.GiantCandidateAllocationCore
public import ArtinMatthews.GiantCandidateCoinSets
public import ArtinMatthews.GiantCandidateFirstEndpoint
public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantTwoSidedPhysicalPairing
public import ArtinMatthews.GiantTwoSidedRootMargin
public import ArtinMatthews.IdealResidualFamily
public import ArtinMatthews.IdealSourceBlocks
public import ArtinMatthews.IdealSourceParameterDefinitions
public import ArtinMatthews.GiantCandidateRetainedSourcePairing
public import ArtinMatthews.GiantCandidateRetainedSourceScalars
public import ArtinMatthews.GiantCandidateSourceAlternation
public import ArtinMatthews.GiantSignedSourceMemoryIdentity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual independent-residue identity closes the source pairing
on each retained dyad at the original reciprocal scale. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem giantCandidateRetainedSourcePairing_eventually
    {Jtest : Type*} [Fintype Jtest] (e : Jtest → ℝ) (he : ∀ j, 0 < e j ∧ e j < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) {mχ : ℕ} (χ : DirichletCharacter ℂ mχ)
    (threshold C Cstep A γ τ : ℝ) (hthreshold : 0 < threshold) (ell j : ℕ)
    (hell : 1 ≤ ell) (hj : 0 < j) {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hC : 0 ≤ C) (hγ : 0 < γ) (hτ : 0 < τ) :
    ∃ Eid : ℝ, 0 < Eid ∧ ∃ m J₀ : ℕ, 1 ≤ m ∧ idealSourceDimensionThreshold m ell ≤ J₀ ∧
      ∀ J : ℕ, J₀ ≤ J →
      ∀ᶠ x : ℝ in atTop,
        let L := Real.log x
        ∀ groups ∈ giantCandidateRetainedOutcomes x threshold,
        let B := GiantCandidatePerformedBig groups
        let PB := giantCandidatePerformedBigBand groups
        let P := fun g : ↥groups => giantCandidateGroup x g.val
        ∃ (B₁ B₂ : Finset B) (hmJ : m ≤ J), Disjoint B₁ B₂ ∧ B₁ ∪ B₂ = Finset.univ ∧
          let family := idealResidualPatterns (idealSourceProbes B₁ hmJ) (idealSourceProbes B₂ hmJ)
          let vmin := Real.log 2/2
          let C₀ := giantCandidateGroupLogRate
          let d := (45/100 : ℝ)
          let Q := ⌊L^(idealSourceRationalExponent (Eid+1) C₀ vmin d m)⌋₊
          let h := L^(-idealSourceWidthExponent (Eid+1) C₀ vmin d C m)
          let ξ := L^(-idealSourceThresholdExponent (Eid+1) C₀ vmin d C m)
          let W := 1 + ((Q : ℝ)^2 / ξ)^2
          (∀ p ∈ family, ∀ g, (idealResidualCopied p g).card ≤ m) ∧
          (family.card : ℝ)*W ≤ L^(idealSourceCostExponent (Eid+1) C₀ vmin d C m) ∧
          let copied (p : IdealResidualPattern B J) := giantCandidatePerformedPattern groups (idealResidualCopied p)
          let K (p : IdealResidualPattern B J) : GiantTwoSidedPatternCoefficient P (copied p) ell :=
            giantCandidatePerformedCoefficient groups (idealResidualCoefficient PB Q h ξ p)
          ∀ (step : ℤ), step ≠ 0 → (step.natAbs : ℝ) ≤ L^Cstep →
          ∀ (ζ : ℝ), |ζ| ≤ L^C →
          ∀ X : ℝ, x^τ ≤ X → X ≤ x^(1/τ) →
          let roots := giantTwoSidedRootInterval X
          let Z := giantTwoSidedRootSlice X
          ∀ u v : ℕ → ℂ, (∀ r ∈ roots, ‖u r‖ ≤ 1) → (∀ r ∈ Z, ‖v r‖ ≤ 1) →
          let F (r : ℕ) := if r ∈ roots then u r * conj (giantCandidateFirstEndpoint e ε x r) else 0
          let G (r : ℕ) := v r * (χ r * giantCandidateAllocationCore (giantCandidateFullPrimes x)
            (Finset.univ.biUnion P) (Real.exp (L^(6/25 : ℝ))) (x^γ) j r)
          let damp (r : ℕ) := (giantTwoSidedEndpointDamping P (J+ell) q r : ℂ)
          ‖giantTwoSidedPhysicalWeightedPairing
            (giantTwoSidedPhysicalFamilyMatrix (Z := Z) family copied step q ζ K)
            (fun s => damp s.val.1.val*F s.val.1.val) (fun s => damp s.val.1.val*G s.val.1.val)/(X:ℂ)‖ ≤
              L^(-A) := by
  obtain ⟨ρ,hρ,hρ1,hqρ⟩ := giantSignedSourceRho_exists hq.le hq1
  let E := max A 0 + ((j*j:ℕ):ℝ)+2
  have hE : 0 ≤ E := add_nonneg (add_nonneg (le_max_right _ _) (Nat.cast_nonneg _)) zero_le_two
  obtain ⟨Eid,hEid,m,J₀,hm,hThreshold,hselect⟩ :=
    giantCandidateRetainedSourcePairing_of_memory_identity e he hε hεq χ threshold C Cstep E γ τ
      hthreshold ell j hell hj hq hq1 hρ hρ1 hqρ hC hE hγ hτ (by
        intro x groups PS PB nzS nzB nzBand nzJoined hPS hPB hdisS hdisB hsep hVS hVB
        intro I k n hn visitQ ν V hb patterns copied κ hκ hsize ζ K θ rows
        have hP (g : GiantCandidatePerformedSmall groups ⊕ GiantCandidatePerformedBig groups)
            (p : ℕ) (hp : p ∈ Sum.elim PS PB g) : p.Prime := by
          cases g with
          | inl g => exact hPS g p hp
          | inr g => exact hPB g p hp
        have hdis : Pairwise (fun a b => Disjoint (Sum.elim PS PB a) (Sum.elim PS PB b)) := by
          intro a b hab
          rcases a with a | a <;> rcases b with b | b
          · exact hdisS (fun h => hab (congrArg Sum.inl h))
          · exact hsep a b
          · exact (hsep b a).symm
          · exact hdisB (fun h => hab (congrArg Sum.inr h))
        exact giantTwoSidedExpandedIndependentFourierMoment_eq_signedMemory (PS := PS)
          patterns copied κ q ρ θ ζ K hP hdis hκ hsize hq hq1 (Nat.pos_of_ne_zero hn)
          (fun g => (hVB g).ne') hρ.ne' (fun p => (hb p).ne'))
  refine ⟨Eid,hEid,m,J₀,hm,hThreshold,?_⟩
  intro J hJ
  filter_upwards [hselect J hJ, giantCandidateRetainedSourcePairing_normalized_log_saving j A,
    eventually_gt_atTop (0 : ℝ)] with x hselect hsave hx
  intro L groups hgroups B PB P
  obtain ⟨B₁,B₂,hmJ,hdis,hunion,hcap,hcost,hbound⟩ := hselect groups hgroups
  refine ⟨B₁,B₂,hmJ,hdis,hunion,hcap,hcost,?_⟩
  intro copied K step hstep0 hstep ζ hζ X hX hXhi roots Z u v hu hv F G damp
  have hXpos : 0 < X := (Real.rpow_pos_of_pos hx τ).trans_le hX
  exact hsave X hXpos _ (hbound step hstep0 hstep ζ hζ X hX hXhi u v hu hv)


theorem giantCandidateFullSourcePairing_eventually
    {Jtest : Type*} [Fintype Jtest] (e : Jtest → ℝ) (he : ∀ j, 0 < e j ∧ e j < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) {mχ : ℕ} (χ : DirichletCharacter ℂ mχ)
    (C Cstep A γ τ : ℝ) (ell j : ℕ)
    (hell : 1 ≤ ell) (hj : 0 < j) {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hC : 0 ≤ C) (hγ : 0 < γ) (hτ : 0 < τ) :
    ∃ Eid : ℝ, 0 < Eid ∧ ∃ m J₀ : ℕ, 1 ≤ m ∧ idealSourceDimensionThreshold m ell ≤ J₀ ∧
      ∀ J : ℕ, J₀ ≤ J →
      ∀ᶠ x : ℝ in atTop,
        let L := Real.log x
        let groups : Finset (GiantCandidateGroupIndex x) := Finset.univ
        let B := GiantCandidatePerformedBig groups
        let PB := giantCandidatePerformedBigBand groups
        let P := fun g : ↥groups => giantCandidateGroup x g.val
        ∃ (B₁ B₂ : Finset B) (hmJ : m ≤ J), Disjoint B₁ B₂ ∧ B₁ ∪ B₂ = Finset.univ ∧
          let family := idealResidualPatterns (idealSourceProbes B₁ hmJ) (idealSourceProbes B₂ hmJ)
          let vmin := Real.log 2/2
          let C₀ := giantCandidateGroupLogRate
          let d := (45/100 : ℝ)
          let Q := ⌊L^(idealSourceRationalExponent (Eid+1) C₀ vmin d m)⌋₊
          let h := L^(-idealSourceWidthExponent (Eid+1) C₀ vmin d C m)
          let ξ := L^(-idealSourceThresholdExponent (Eid+1) C₀ vmin d C m)
          let W := 1 + ((Q : ℝ)^2 / ξ)^2
          (∀ p ∈ family, ∀ g, (idealResidualCopied p g).card ≤ m) ∧
          (family.card : ℝ)*W ≤ L^(idealSourceCostExponent (Eid+1) C₀ vmin d C m) ∧
          let copied (p : IdealResidualPattern B J) := giantCandidatePerformedPattern groups (idealResidualCopied p)
          let K (p : IdealResidualPattern B J) : GiantTwoSidedPatternCoefficient P (copied p) ell :=
            giantCandidatePerformedCoefficient groups (idealResidualCoefficient PB Q h ξ p)
          ∀ (step : ℤ), step ≠ 0 → (step.natAbs : ℝ) ≤ L^Cstep →
          ∀ (ζ : ℝ), |ζ| ≤ L^C →
          ∀ X : ℝ, x^τ ≤ X → X ≤ x^(1/τ) →
          let roots := giantTwoSidedRootInterval X
          let Z := giantTwoSidedRootSlice X
          ∀ u v : ℕ → ℂ, (∀ r ∈ roots, ‖u r‖ ≤ 1) → (∀ r ∈ Z, ‖v r‖ ≤ 1) →
          let F (r : ℕ) := if r ∈ roots then u r * conj (giantCandidateFirstEndpoint e ε x r) else 0
          let G (r : ℕ) := v r * (χ r * giantCandidateAllocationCore (giantCandidateFullPrimes x)
            (Finset.univ.biUnion P) (Real.exp (L^(6/25 : ℝ))) (x^γ) j r)
          let damp (r : ℕ) := (giantTwoSidedEndpointDamping P (J+ell) q r : ℂ)
          ‖giantTwoSidedPhysicalWeightedPairing
            (giantTwoSidedPhysicalFamilyMatrix (Z := Z) family copied step q ζ K)
            (fun s => damp s.val.1.val*F s.val.1.val) (fun s => damp s.val.1.val*G s.val.1.val)/(X:ℂ)‖ ≤
              L^(-A) := by
  have hrate : 0 < giantCandidatePerformedLowerRate := by
    unfold giantCandidatePerformedLowerRate
    positivity
  obtain ⟨Eid,hEid,m,J₀,hm,hThreshold,hselect⟩ :=
    giantCandidateRetainedSourcePairing_eventually e he hε hεq χ
      giantCandidatePerformedLowerRate C Cstep A γ τ hrate ell j hell hj hq hq1 hC hγ hτ
  refine ⟨Eid,hEid,m,J₀,hm,hThreshold,?_⟩
  intro J hJ
  filter_upwards [hselect J hJ, giantCandidateFullSelection_retained_eventually] with x hx hfull
  exact hx Finset.univ hfull

end
end ArtinMatthews
