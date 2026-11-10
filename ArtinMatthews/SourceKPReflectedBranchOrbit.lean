module

public import ArtinMatthews.SourceKPReflectedBranchData
public import ArtinMatthews.SourceReflectionRotatedMass
public import ArtinMatthews.SourceKPReflectedPhysicalPointwise
public import ArtinMatthews.SourceKPReflectedPhysicalSupport
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

/-! The supported actual Fourier series, with the original finite
tensors still grouped, gives the precise norm-one orbit sum. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic
open SourcePhysical SourceReflection SourceEulerAssembly
open scoped NumberField Classical BigOperators
noncomputable section
set_option quotPrecheck false

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "X" => ExteriorUnitSixthClasses S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "Whole" => SWholeUnits K S
local notation "N" => SNormOne K S
local notation "D" => sWholeDiagonal K S
local notation "sc" => sLocalPositiveScaling K hζ S
local notation "rep" => sourceExteriorUnitSixthRepresentative S
local notation "arg" => sourceKPSLocalReflectionArgument K S
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
local notation "b[" f "," d "]" => gen (sourceReflectionActiveExponents K S₀ f+d)
local notation "I[" f "," d "]" => SourceReflectionSupportedTermIndex K S₀ f d
local notation "ω" => fun b => sourceKPReflectionProductPhase K hζ b
  (sourceKPOrientedHorizontal K hζ) (sourceKPAllInfinitePlaces K)
local notation "A" => sourceKPReflectedArchBesselFactor K S₀
local notation "C₁" => sourceKPCuspResidualFourierValue K hζ (1 : Kˣ)
local notation "L" => sourceKPLocalCompactProductLift K hζ S
local notation "Ω" => sourceKPTameUniformizerCharacter K hζ
local notation "σ" => sourceKPTraceJacquetFrequencyAt K
local notation "hs" => sourceKPReflectedRetained_parameter_pos
local notation "Basis" => SourceKPAdelicOutgoingRetainedJacquetLabel K hζ hs S
local notation "Seed[" p "]" => SourceKPRetainedSeedIndex K S (p).R (p).M
local notation "Label[" p "]" => SourceKPReflectedRetainedLabel K hζ S₀ (p).R (p).M
local notation "F" => sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile K hζ
local notation "lift" => sourceKPAdelicOutgoingRetainedJacquetBasisLift K hζ
local notation "pre[" p "]" => sourceKPAdelicOutgoingReflectedRetainedPrefix K hζ S₀ (p).R (p).M

attribute [local instance] sourceKPReflectedRetainedLabel_fintype
local notation "χ" => sourceKPPhysicalRowFiniteCharacter K hζ S₀
local notation "cs" => sourceKPReflectedRetainedSeedScalar K hζ S₀
local notation "TV" => sourceKPReflectedRetainedTensorValue K hζ S₀
local notation "BD" => sourceKPReflectedRetainedTensor K hζ S₀
local notation "BC" => sourceKPReflectedBranchCoefficient K hζ S₀
local notation "BA" => sourceKPReflectedBranchArithmetic K hζ S₀
local notation "raw" => sourceKPReflectedPhysicalBranchTerm K hζ S₀
local notation "G" => sourceKPReflectedPhysicalBranchValue K hζ S₀
local notation "m₀" => sourceKPReflectedNumerator K hζ S₀
local notation "cl" => sWholeGlobalClassMap K 6 S

variable {J : Ideal (𝓞 K)} {T : ℝ}

theorem sourceKPReflectedBranchTerm_eq_tensors
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (hcut : principalAngularCutoff K J ⊆ S)
    (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (h d : E) (f : Finset PE) (hf : f ∈ sourceReflectionActiveChoices K S₀ h)
    (hd : sourceReflectionIsSquarefree d) (hdh : Disjoint d.support h.support)
    (u ε : X) (v : InfinitePlace K) (i : I[f,d]) (γ : Γ) (x : Whole) :
    let b := b[f,d]
    let m := m₀ f d i ε γ
    ω b * raw hS η hJ hT p (h+d) u (f∪d.support) b m x =
      ∑ l : Label[p], BC hS η hJ hT p u ε h d f i.val l * TV hS η hJ hT p u v l (D m*x) := by
  let b := b[f,d]
  let m := m₀ f d i ε γ
  let z := D m*x
  let g := sourceKPRetainedNegativeClass K hζ S₀ (cl ((b⁻¹)^2)) (cl m)
  let c₀ := C₁ (one_le_two.trans hT.le) (sourceKPPositiveSeedData_q₀ K hζ S₀ p)
  let a := sourceKPPhysicalNegativePhase K hζ S₀ hS η hJ (rep u) b (D m)
  let e := sourceReflectionSignedExteriorProduct K S₀ hζ hS (h+d) (f∪d.support) (m/b^2)
  let c (k : Seed[p] × Basis) :=
    sourceKPRetainedSeedWeight K S p.R p.M k.1 *
      C₁ (one_le_two.trans hT.le) ((L (fun P => lift P.val hs (k.2 P))).2)
  let V (k : Seed[p] × Basis) := ∏ P : S, F P.val hs (k.2 P) (pre[p] k.1 p.a P) (z.2 P)
  let k₀ := sourceKPAllowedClassGate K hζ S₀ (arg b*x⁻¹)
  let w := sourceKPReflectedC1WeylPhase K hζ S₀ b z
  let o := ∏ P : S, (Ω P.val (σ P.val m) (z.2 P) : ℂ)
  let χ₁ := (χ hS η hJ (rep u) z : ℂ)
  have hc : (∑ k : Seed[p] × Basis, cs hS hJ hT p k * V k) =
      c₀⁻¹ * ∑ k : Seed[p] × Basis, c k * V k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    change (c₀⁻¹*c k)*V k = c₀⁻¹*(c k*V k)
    exact mul_assoc _ _ _
  have hclass : g (sourceKPRetainedFiniteSixthClass K S z.2) = k₀*w*o :=
    sourceKPRetainedNegativeClass_eq K hζ S₀ b m x
  have hsum := sourceKPReflectedRetainedTensor_sum K hζ S₀ hS η hJ hT p u v g
    (cs hS hJ hT p) z
  change g _ * χ₁ * A z * (∑ k, cs hS hJ hT p k * V k) = _ at hsum
  have harith (l : Label[p]) : BA hS η hJ u ε h d f i.val l.2.2 = e*a*g l.2.2 :=
    sourceKPReflectedBranchArithmetic_supported K hζ S₀ hS η hJ hcut
      u ε h d f hf hd hdh i γ l.2.2
  let U₀ := ∑ k : Seed[p] × Basis, c k * V k
  let U₁ := ∑ k : Seed[p] × Basis, cs hS hJ hT p k * V k
  let G₀ := g (sourceKPRetainedFiniteSixthClass K S z.2)
  let A₀ := A z
  let W (l : Label[p]) := TV hS η hJ hT p u v l z
  let s (l : Label[p]) := cs hS hJ hT p (l.1,l.2.1)
  change ω b * raw hS η hJ hT p (h+d) u (f∪d.support) b m x = _
  calc
    _ = a * c₀⁻¹ * k₀ * χ₁ * w * e * o * U₀ * A₀ :=
      sourceKPReflectedPhysicalBranchTerm_retainedTensor K hζ S₀ hS η hJ hT p h d f hf u m x hs
    _ = e*a * ((k₀*w*o) * χ₁ * A₀ * (c₀⁻¹*U₀)) := by ac_rfl
    _ = e*a * (G₀ * χ₁ * A₀ * U₁) :=
      congrArg₂ (fun q u => e*a*(q*χ₁*A₀*u)) hclass.symm hc.symm
    _ = e*a * ∑ l : Label[p], s l * g l.2.2 * W l :=
      congrArg (fun t : ℂ => e*a*t) hsum
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      change e*a * (s l * g l.2.2 * W l) =
        (BA hS η hJ u ε h d f i.val l.2.2 * s l) * W l
      calc
        _ = (e*a*g l.2.2) * s l * W l := by ac_rfl
        _ = _ := congrArg (fun t : ℂ => t * s l * W l) (harith l).symm

theorem sourceKPReflectedBranchOrbit_hasSum
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (hcut : principalAngularCutoff K J ⊆ S)
    (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (h d : E) (f : Finset PE) (hf : f ∈ sourceReflectionActiveChoices K S₀ h)
    (hd : sourceReflectionIsSquarefree d) (hdh : Disjoint d.support h.support)
    (u : X) (v : InfinitePlace K) (t : ℝ) (n : N) :
    let b := b[f,d]
    HasSum (fun q : (I[f,d] × X) × Γ =>
      ∑ l : Label[p], sourceReflectionRotatedTerm K S₀ hζ v (BD hS η hJ hT p u v) f
        (fun _ => l) (fun i => BC hS η hJ hT p u q.1.2 h d f i l) (fun _ _ => 1)
        q.1.1.val (((n*q.2.val : N) : Whole) *
          sourceKPReflectedBranchDilation K hζ S₀ q.1.2 f t q.1.1.val))
      (ω b * G hS η hJ hT p (h+d) u (f∪d.support) b ((n : Whole)*sc t)) := by
  let x := (n : Whole)*sc t
  let b := b[f,d]
  let e : (I[f,d] × X) × Γ ≃ I[f,d] × (X × Γ) := Equiv.prodAssoc _ _ _
  have hsum := (sourceKPReflectedPhysicalBranchTerm_hasSum_supported K hζ S₀ hS η hJ hT
    p h d f hf hd hdh.symm u x).mul_left (ω b)
  have hsum' := e.hasSum_iff.mpr hsum
  refine hsum'.congr_fun ?_
  intro q
  change (∑ l : Label[p], _) =
    ω b * raw hS η hJ hT p (h+d) u (f∪d.support) b (m₀ f d q.1.1 q.1.2 q.2) x
  rw [sourceKPReflectedBranchDilation_orbit K hζ S₀ q.1.2 f d t q.1.1 q.2 n]
  simp only [sourceReflectionRotatedTerm,one_mul]
  exact (sourceKPReflectedBranchTerm_eq_tensors K hζ S₀ hS η hJ hcut hT p h d f hf hd hdh
    u q.1.2 v q.1.1 q.2 x).symm

end
end ArtinMatthews
