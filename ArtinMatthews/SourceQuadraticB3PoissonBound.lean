module

public import ArtinMatthews.SourceQuadraticB2Base
public import ArtinMatthews.QuadraticB2PoissonCutoff
public import ArtinMatthews.SourceReflectionExteriorRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The analytic input is Goldmakher–Louvel Proposition 5.2 on the
actual annular B3 block. Its common-ideal sum is bounded here using
the fixed-field count of exterior ideals. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {G : Type} [Fintype G] [DecidableEq G]

local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

/-- The real part of the literal B3 block on a column annulus. The
class label is fixed throughout the descent. -/
def SourceQuadraticB3PoissonBound (label : E → G) (a : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ M P K : ℝ, 1 ≤ M → 1 ≤ P →
    P ^ 2 / M * (M * P) ^ δ ≤ K → K ≤ M * (M * P) ^ (-δ) →
    ∀ cols : Finset E,
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ P < (q b : ℝ) ∧ (q b : ℝ) ≤ 2 * P) →
      ∀ c : G, ∀ g ∈ sourceQuadraticCommonIdeals F S₀
        (sourceQuadraticClassColumns F S₀ cols label c), ∀ u : E → ℂ,
        (sourceQuadraticB3Block F S₀ hζ (sourceQuadraticB2Rows F S₀ M K)
          (sourceQuadraticClassColumns F S₀ cols label c)
          (sourceQuadraticB2RowWeight F S₀ M) u g).re ≤
        (C * (q g : ℝ) ^ 4 * (M * P) ^ δ *
          (M + P + Real.sqrt M * K ^ (a - 1 / 2) + Real.sqrt (M / K) * P)) *
          coeffMass (sourceQuadraticClassColumns F S₀ cols label c) u

theorem exists_sourceQuadraticB2AnnularStep (label : E → G) {a δ : ℝ}
    (ha : 1 ≤ a) (hδ : 0 < δ) (hpoisson : SourceQuadraticB3PoissonBound F S₀ hζ label a) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ M N L H P : ℝ, 1 ≤ M → 1 ≤ N → 1 ≤ L → L ≤ N →
      1 ≤ H → 1 ≤ P → P ≤ L → 2 * N * (M * N) ^ δ ≤ M →
      ∀ (cols : Finset E) (u : E → ℂ),
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ P < (q b : ℝ) ∧
        (q b : ℝ) ≤ 2 * P ∧ (q b : ℝ) ≤ L) →
      let K := poissonCutoff M N δ
      sourceQuadraticB2Energy F S₀ hζ (sourceQuadraticB2Rows F S₀ M K) cols
          (sourceQuadraticB2RowWeight F S₀ M) u ≤
        (B * (M * N) ^ (δ * (a + 1 / 2)) *
          (sourceQuadraticSmoothedB2Norm F S₀ hζ M K (L / H) +
            H ^ 5 * poissonMainScale M N a)) * coeffMass cols u := by
  obtain ⟨C, hC, hCbound⟩ := hpoisson δ hδ
  obtain ⟨D, hD, hred⟩ := sourceQuadraticB2Energy_class_common_reduction F S₀ hζ δ hδ
  obtain ⟨A, hA, hcount⟩ := exists_sourceReflectionExteriorCard_le F S₀
  let γ : ℝ := Fintype.card G
  let B := (1 + γ) * (1 + D + 3 * C * A)
  have hγ : 0 ≤ γ := Nat.cast_nonneg _
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le (by linarith)
    (by nlinarith [mul_nonneg hC.le hA.le])
  refine ⟨B, hB, ?_⟩
  intro M N L H P hM hN hL hLN hH hP hPL hsep cols u hcols K
  let T := M * N
  let loss := T ^ (δ * (a + 1 / 2))
  let main := poissonMainScale M N a
  let rows := sourceQuadraticB2Rows F S₀ M K
  let w := sourceQuadraticB2RowWeight F S₀ M
  let tail := sourceQuadraticSmoothedB2Norm F S₀ hζ M K (L / H)
  let cl (c : G) := sourceQuadraticClassColumns F S₀ cols label c
  let small (c : G) := sourceQuadraticSmallCommonIdeals F S₀ (cl c) H
  have hM0 := zero_lt_one.trans_le hM
  have hN0 := zero_lt_one.trans_le hN
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hM hN
  have hT0 := zero_lt_one.trans_le hT
  have hmain : 0 ≤ main := poissonMainScale_nonneg hM0.le hN0.le a
  have hloss : 0 ≤ loss := Real.rpow_nonneg hT0.le _
  have htail : 0 ≤ tail := sourceQuadraticB2Norm_nonneg F S₀ hζ _ _ _
  have hH0 := zero_lt_one.trans_le hH
  have hm : 0 ≤ coeffMass cols u := coeffMass_nonneg _ _
  have hPgeom := poissonCutoff_range hM hN hδ.le hsep hP (hPL.trans hLN)
  have hPcost := poissonCutoff_block_le hM hN hP (hPL.trans hLN) hδ.le ha
  have hpowP : (M * P) ^ δ ≤ T ^ δ :=
    Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left (hPL.trans hLN) hM0.le) hδ.le
  have hcombine : T ^ δ * T ^ (δ * (a - 1 / 2)) = loss := by
    rw [← Real.rpow_add hT0]
    congr 1
    ring
  have hbase (c : G) (g : E) (hg : g ∈ small c) :
      (sourceQuadraticB3Block F S₀ hζ rows (cl c) w u g).re ≤
        (3 * C * (q g : ℝ) ^ 4 * loss * main) * coeffMass (cl c) u := by
    have hg' : g ∈ sourceQuadraticCommonIdeals F S₀ (cl c) := (Finset.mem_filter.mp hg).1
    have hm' := coeffMass_nonneg (cl c) u
    refine (hCbound M P K hM hP hPgeom.2.2.1 hPgeom.2.2.2 cols
      (fun b hb => ⟨(hcols b hb).1, (hcols b hb).2.1, (hcols b hb).2.2.1⟩) c g hg' u).trans ?_
    have hK0 : 0 ≤ K := zero_le_one.trans hPgeom.1
    have hP0 : 0 ≤ P := zero_le_one.trans hP
    have hzero : 0 ≤ M + P + Real.sqrt M * K ^ (a - 1 / 2) + Real.sqrt (M / K) * P := by
      positivity
    calc
      _ ≤ ((C * (q g : ℝ) ^ 4) * T ^ δ *
          (3 * main * T ^ (δ * (a - 1 / 2)))) * coeffMass (cl c) u := by
        apply mul_le_mul_of_nonneg_right _ hm'
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpowP (by positivity))
          hPcost hzero (by positivity)
      _ = _ := by rw [← hcombine]; ring
  have hsmall (c : G) :
      (∑ g ∈ small c, (sourceQuadraticB3Block F S₀ hζ rows (cl c) w u g).re) ≤
        ((3 * C * A) * loss * (H ^ 5 * main)) * coeffMass (cl c) u := by
    have hHq (g : E) (hg : g ∈ small c) : (q g : ℝ) ≤ H := (Finset.mem_filter.mp hg).2
    have hcard := hcount H hH (small c) hHq
    have hsum : (∑ g ∈ small c, (q g : ℝ) ^ 4) ≤ A * H ^ 5 := by
      calc
        _ ≤ ∑ _g ∈ small c, H ^ 4 :=
          Finset.sum_le_sum (fun g hg => pow_le_pow_left₀ (Nat.cast_nonneg _) (hHq g hg) 4)
        _ = (small c).card * H ^ 4 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (A * H) * H ^ 4 := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring
    calc
      _ ≤ ∑ g ∈ small c, (3 * C * (q g : ℝ) ^ 4 * loss * main) * coeffMass (cl c) u :=
        Finset.sum_le_sum (hbase c)
      _ = ((3 * C * loss * main) * ∑ g ∈ small c, (q g : ℝ) ^ 4) * coeffMass (cl c) u := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        ring
      _ ≤ ((3 * C * loss * main) * (A * H ^ 5)) * coeffMass (cl c) u :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by positivity))
          (coeffMass_nonneg _ _)
      _ = _ := by ring
  have hsum : (∑ c : G, ∑ g ∈ small c, (sourceQuadraticB3Block F S₀ hζ rows (cl c) w u g).re) ≤
      ((3 * C * A) * loss * (H ^ 5 * main)) * coeffMass cols u := by
    calc
      _ ≤ ∑ c : G, ((3 * C * A) * loss * (H ^ 5 * main)) * coeffMass (cl c) u :=
        Finset.sum_le_sum (fun c _ => hsmall c)
      _ = _ := by rw [← Finset.mul_sum, sourceQuadratic_coeffMass_class_sum F S₀ cols label u]
  have hLloss : L ^ δ ≤ loss := by
    refine (Real.rpow_le_rpow (zero_le_one.trans hL)
      (hLN.trans (le_mul_of_one_le_left hN0.le hM)) hδ.le).trans ?_
    exact Real.rpow_le_rpow_of_exponent_le hT
      (le_mul_of_one_le_right hδ.le (by linarith))
  have hsmallcoef : γ * (3 * C * A) ≤ B := by
    have h : 0 ≤ 3 * C * A := by positivity
    dsimp [B]
    nlinarith [mul_nonneg hγ hD.le]
  have htailcoef : γ * D ≤ B := by
    have h : 0 ≤ γ * (3 * C * A) := by positivity
    dsimp [B]
    nlinarith
  calc
    _ ≤ γ * ((∑ c : G, ∑ g ∈ small c,
        (sourceQuadraticB3Block F S₀ hζ rows (cl c) w u g).re) +
        (D * L ^ δ * tail) * coeffMass cols u) :=
      hred hL (zero_lt_one.trans_le hH) rows cols w
        (fun _ _ => sourceQuadraticB2Bump_nonneg _)
        (fun b hb => ⟨(hcols b hb).2.2.2, (hcols b hb).1⟩) u label
    _ ≤ γ * (((3 * C * A) * loss * (H ^ 5 * main)) * coeffMass cols u +
        (D * loss * tail) * coeffMass cols u) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hsum (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLloss hD.le) htail) hm)) hγ
    _ = ((γ * (3 * C * A)) * loss * (H ^ 5 * main) + (γ * D) * loss * tail) *
        coeffMass cols u := by ring
    _ ≤ (B * loss * (H ^ 5 * main) + B * loss * tail) * coeffMass cols u := by
      exact mul_le_mul_of_nonneg_right
        (add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsmallcoef hloss) (by positivity))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htailcoef hloss) htail)) hm
    _ = _ := by ring

end
end ArtinMatthews.SourceEulerAssembly
