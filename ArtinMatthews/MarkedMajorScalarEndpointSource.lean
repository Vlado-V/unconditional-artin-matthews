module

public import ArtinMatthews.MarkedMajorScalarEndpointMean
public import ArtinMatthews.MarkedTypeIIScalarDeterminantComparison
public import ArtinMatthews.MarkedMajorArcCircleSource
public import ArtinMatthews.MarkedMajorLabelEndpointIdentity
public import ArtinMatthews.MarkedMajorEndpointTriple
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal finite endpoints for the scalar major form. The dyadic label
cutoff, both coefficients, and the original signed detector are retained. -/
namespace ArtinMatthews
open Finset
open scoped ComplexConjugate
noncomputable section

variable {J : Type*} [Fintype J]

def markedMajorScalarTripleSet (P : J → Finset ℕ) (Y : ℝ) (S T : Finset ℕ) :
    Finset (ℕ×(ℕ×ℕ)) :=
  markedTypeIIDyadLabels P Y ×ˢ (S×ˢT)

def markedMajorScalarBare (P : J → Finset ℕ) (η : ℝ → ℂ) (Y : ℝ)
    (α β : ℕ → ℂ) (z : ℕ×(ℕ×ℕ)) : ℂ :=
  η ((z.1:ℝ)/Y)*(markedMajorLabelMass P:ℂ)*α z.2.1*β z.2.2

def markedMajorScalarTripleWeight (P : J → Finset ℕ) (η : ℝ → ℂ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (θ Y : ℝ) (α β : ℕ → ℂ) (z : ℕ×(ℕ×ℕ)) : ℂ :=
  markedMajorLabelWeight P η χ θ Y z.1*α z.2.1*β z.2.2

theorem markedTypeIIScalarFullMajor_eq_kernelSource (P : J → Finset ℕ) (S T : Finset ℕ)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q Y : ℝ) (α β : ℕ → ℂ)
    (hY : 0 < Y) (hη : Function.support η ⊆ Set.Icc 1 4) :
    markedTypeIIScalarFullMajor P S T η ψ Q Y α β =
      markedMajorKernelSource (markedMajorScalarTripleSet P Y S T) (markedMajorScalarTripleSet P Y S T)
        (markedMajorScalarBare P η Y α β)
        (markedMajorScalarBare P η Y (fun m => conj (α m)) (fun n => conj (β n))) ψ Q Y := by
  unfold markedTypeIIScalarFullMajor
  rw [Finset.product_eq_sprod,markedTypeIIScalarMajorOn_dyad P S S T η ψ Q Y hY hη]
  let L := markedTypeIIDyadLabels P Y
  let V := S×ˢT
  unfold markedTypeIIScalarMajorOn markedMajorKernelSource markedMajorScalarTripleSet
  simp only [show markedTypeIIDyadLabels P Y=L from rfl,show S×ˢT=V from rfl,
    Finset.sum_product (s:=L) (t:=L),Finset.sum_product (s:=L) (t:=V),one_mul,mul_sum]
  apply sum_congr rfl
  intro b _
  rw [sum_comm (s:=L) (t:=V)]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro w _
  simp only [markedTypeIIScalarMajorTerm,markedMajorScalarBare]
  ring

theorem markedMajorScalarTripleSet_compact (P : J → Finset ℕ) (Y H U : ℝ)
    (S T : Finset ℕ) (hY : 0 < Y) (hH : 0 < H) (hU : 0 < U)
    (hS : ∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H)
    (hT : ∀ n ∈ T,U ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*U)
    (z : ℕ×(ℕ×ℕ)) (hz : z ∈ markedMajorScalarTripleSet P Y S T) :
    markedMajorLabelTripleValue z/(Y*(H*U)) ∈ Set.Icc (1/2:ℝ) 32 := by
  obtain ⟨hb,hm,hn⟩ := by simpa only [markedMajorScalarTripleSet,mem_product] using hz
  obtain ⟨hb₁,hb₂⟩ := (mem_filter.mp hb).2
  have hZ := mul_pos hY (mul_pos hH hU)
  have hlo : Y*(H*U) ≤ (z.1:ℝ)*z.2.1*z.2.2 := by
    calc
      _ = (Y*H)*U := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul hb₁ (hS _ hm).1 hH.le (Nat.cast_nonneg _))
        (hT _ hn).1 hU.le (by positivity)
  have hhi : (z.1:ℝ)*z.2.1*z.2.2 ≤ 16*(Y*(H*U)) := by
    calc
      _ ≤ ((4*Y)*(2*H))*(2*U) := mul_le_mul
        (mul_le_mul hb₂ (hS _ hm).2 (Nat.cast_nonneg _) (by positivity))
        (hT _ hn).2 (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  simp only [Set.mem_Icc,markedMajorLabelTripleValue,Nat.cast_mul]
  exact ⟨(le_div_iff₀ hZ).mpr (by linarith), (div_le_iff₀ hZ).mpr (by linarith)⟩

theorem markedMajorScalarPolynomial_eq_sum (S : Finset ℕ) (H : ℝ) (α : ℕ → ℂ) (t : ℝ) :
    markedMajorScalarPolynomial S H α t = (∑ m ∈ S,α m*markedPrimePhase m t)/(H:ℂ) := by
  unfold markedMajorScalarPolynomial markedNaturalPolynomial
  rw [sum_div]
  apply sum_congr rfl
  intro m _
  ring

theorem markedMajorScalarEndpoint_source
    (P : J → Finset ℕ) (η : ℝ → ℂ) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (θ Y H U : ℝ) (S T : Finset ℕ) (α β : ℕ → ℂ)
    (hY : 0 < Y) (hH : 0 < H) (hU : 0 < U) (hη : Function.support η ⊆ Set.Icc 1 4)
    (hS : ∀ m ∈ S,0 < m) (hT : ∀ n ∈ T,0 < n) (t : ℝ) :
    markedMajorEndpointPolynomial (markedMajorScalarTripleSet P Y S T)
      (markedMajorScalarTripleWeight P η χ θ Y α β) markedMajorLabelTripleValue t =
        ((Y*(H*U):ℝ):ℂ)*markedMajorScalarEndpoint P η χ θ Y H U S T α β t := by
  have hlabel : (∑ b ∈ markedTypeIIDyadLabels P Y,
      markedMajorLabelWeight P η χ θ Y b*markedPrimePhase b t) =
      ∑ b ∈ markedMajorLabelSet P,markedMajorLabelWeight P η χ θ Y b*markedPrimePhase b t := by
    apply sum_subset (filter_subset _ _)
    intro b hb hd
    have hzero : η ((b:ℝ)/Y)=0 := by
      by_contra hn
      obtain ⟨hlo,hhi⟩ := hη hn
      exact hd (mem_filter.mpr ⟨hb,by
        rw [le_div_iff₀ hY] at hlo
        rw [div_le_iff₀ hY] at hhi
        simpa only [one_mul] using And.intro hlo hhi⟩)
    simp only [markedMajorLabelWeight,hzero,zero_mul]
  unfold markedMajorScalarTripleSet markedMajorScalarTripleWeight markedMajorLabelTripleValue
  rw [markedMajorEndpointPolynomial_triple _ _ _ _ α β
    (fun b hb => Nat.cast_pos.mp (hY.trans_le (mem_filter.mp hb).2.1)) hS hT,hlabel]
  unfold markedMajorScalarEndpoint
  rw [markedMajorScalarPolynomial_eq_sum,markedMajorScalarPolynomial_eq_sum]
  have hb : markedMajorLabelPolynomial P η χ θ Y t =
      (Y:ℂ)⁻¹*∑ b ∈ markedMajorLabelSet P,
        markedMajorLabelWeight P η χ θ Y b*markedPrimePhase b t := rfl
  rw [hb]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hY.ne',Complex.ofReal_ne_zero.mpr hH.ne',
    Complex.ofReal_ne_zero.mpr hU.ne']

end
end ArtinMatthews
