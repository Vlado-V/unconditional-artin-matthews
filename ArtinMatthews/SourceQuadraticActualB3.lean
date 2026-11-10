module

public import ArtinMatthews.SourceQuadraticDualOffDiagonalBound
public import ArtinMatthews.SourceQuadraticB3PoissonBound
public import ArtinMatthews.SourceQuadraticB3SquarefreeTail
public import ArtinMatthews.SourceQuadraticClassFactorization
public import ArtinMatthews.SourceQuadraticSmallError
public import ArtinMatthews.QuadraticB3TailScale
public import ArtinMatthews.SourceQuadraticActualSignedResidue
public import ArtinMatthews.SourceQuadraticB3ComponentBound
public import ArtinMatthews.SourceQuadraticB3SquarefreeTailBound
public import ArtinMatthews.SourceQuadraticSmallClassBound
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale StandardAdelic
open scoped NumberField Classical
noncomputable section

private theorem component_scale_mono (c a l x y m : ℝ)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hl : 0 ≤ l) (hm : 0 ≤ m) (hxy : x ≤ y) :
    c * a * l * x * m ≤ c * a * l * y * m :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxy
    (mul_nonneg (mul_nonneg hc ha) hl)) hm

private theorem component_scale_enlarge (c x y a l m : ℝ)
    (hc : 0 ≤ c) (hx : 0 ≤ x) (hxy : x ≤ y) (ha : 1 ≤ a) (hl : 1 ≤ l)
    (hm : 0 ≤ m) : c * x * m ≤ c * a * l * y * m := by
  have h : x ≤ a * l * y :=
    hxy.trans (le_mul_of_one_le_left (hx.trans hxy) (one_le_mul_of_one_le_of_one_le ha hl))
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hc) hm

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

/-- The original actual ray-class B3 estimate, with all analytic components proved. -/
theorem sourceQuadraticB3PoissonBound_actual
    [Fintype (SourceQuadraticRayClass F S₀)]
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀) {α : ℝ} (hα : 1 ≤ α)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α) :
    SourceQuadraticB3PoissonBound F S₀ hζ (sourcePrimeExponentRayClass F S₀) α := by
  intro δ hδ
  obtain ⟨Cd, hCd, hdiag⟩ := sourceQuadraticDiagonalBlock_bounds F S₀ hζ
  obtain ⟨Ce, hCe, herr⟩ := sourceQuadraticDualOffDiagonalErrorBlock_bound F S₀ hζ hα htrace hE δ hδ
  obtain ⟨Ct, hCt, htail⟩ := sourceQuadraticB3SquarefreeTail_bound F S₀ hζ δ hδ
  obtain ⟨Cs, hCs, hsmall⟩ := sourceQuadraticOriginalSmallErrorBlock_rayClass_bound F S₀ hζ htrace hE δ hδ
  obtain ⟨Cr, hCr, hres⟩ := sourceQuadraticActualSignedResidueBlock_annular_bound F S₀ hζ htrace hE δ hδ
  refine ⟨Cd + Ce + Ct + Cs + Cr, by positivity, ?_⟩
  intro M P K hM hP hlower hupper cols hcols κ g hg u
  let D := sourceQuadraticClassColumns F S₀ cols (sourcePrimeExponentRayClass F S₀) κ
  let Q : ℝ := (q g : ℝ) ^ 4
  let L : ℝ := (M * P) ^ δ
  let A : ℝ := Real.sqrt M * K ^ (α - 1 / 2)
  let R : ℝ := Real.sqrt (M / K) * P
  let S : ℝ := M + P + A + R
  let m : ℝ := coeffMass D u
  let B : ℝ := Q * L * S * m
  have hM0 := zero_lt_one.trans_le hM
  have hP0 := zero_lt_one.trans_le hP
  obtain ⟨hK, hKM, _⟩ := quadraticB3_cutoff_range hM hP hδ hlower hupper
  have hm : 0 ≤ m := coeffMass_nonneg _ _
  have hQ : 1 ≤ Q := by
    exact one_le_pow₀ (sourceReflection_norm_one_le F S₀ g)
  have hL : 1 ≤ L := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hM hP) hδ.le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hDM (b : E) (hb : b ∈ D) : b ∈ cols := (Finset.mem_filter.mp hb).1
  have hDsf (b : E) (hb : b ∈ D) : sourceReflectionIsSquarefree b := (hcols b (hDM b hb)).1
  have hDclass (b : E) (hb : b ∈ D) (c : E) (hc : c ∈ D) :
      sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c := by
    exact sourcePrimeExponentRayClass_eq_localClass F S₀ hζ b c
      ((Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp hc).2.symm)
  have hDcols (b : E) (hb : b ∈ D) :
      sourceReflectionIsSquarefree b ∧ P ≤ (q b : ℝ) ∧ (q b : ℝ) ≤ 2 * P :=
    ⟨hDsf b hb, (hcols b (hDM b hb)).2.1.le, (hcols b (hDM b hb)).2.2⟩
  have hd : ‖sourceQuadraticZeroResidualBlock F S₀
      (sourceQuadraticBlockIdealFull F S₀ hζ M g) D u g‖ ≤ Cd * B := by
    refine ((hdiag M hM D u g).1).trans ?_
    simpa only [B, mul_assoc] using component_scale_enlarge Cd M S Q L m hCd.le hM0.le
      (by dsimp [S]; linarith) hQ hL hm
  have he : ‖sourceQuadraticNonzeroResidualBlock F S₀
      (sourceQuadraticDualDivisorError F S₀ hζ M K (quadraticDualErrorLine δ) g) D u g‖ ≤ Ce * B := by
    rw [sourceQuadraticNonzeroResidualBlock_eq_offDiagonal]
    have hb := herr M K P hM hK.le hKM hP D hDcols hDclass u g
    refine hb.trans ?_
    simpa only [B, A, Q, L, m, mul_assoc] using component_scale_mono Ce Q L (M + A) S m
      hCe.le (zero_le_one.trans hQ) (zero_le_one.trans hL) hm (by dsimp [S]; linarith)
  have ht : ‖sourceQuadraticNonzeroResidualBlock F S₀
      (sourceQuadraticDualDivisorTail F S₀ hζ M K g) D u g‖ ≤ Ct * B := by
    rw [sourceQuadraticNonzeroResidualBlock_eq_offDiagonal]
    have hb := htail M P K hM hP hlower hupper cols (fun b hb => (hcols b hb).1)
      (fun b hb => (hcols b hb).2.2) κ g u α
    simpa only [sourceQuadraticB3SquarefreeTail, B, Q, L, S, A, R, m, D, mul_assoc] using hb
  have hs : ‖sourceQuadraticOriginalSmallErrorBlock F S₀ hζ M K (quadraticSmallErrorLine δ)
      D u g‖ ≤ Cs * B := by
    have hb := hsmall M K P hM hP hK.le hKM cols hcols κ g hg u
    refine hb.trans ?_
    have hscale := component_scale_enlarge (Cs * L) (P + A) S Q 1 m
      (mul_nonneg hCs.le (zero_le_one.trans hL)) (by positivity)
      (by dsimp [S]; linarith) hQ (by norm_num) hm
    convert hscale using 1
    dsimp [B, Q, L, A, m]
    ring
  have hr : ‖sourceQuadraticCommonPairBlock F S₀ (fun e =>
      sourceQuadraticDualDivisorResidue F S₀ hζ M K g e -
      sourceQuadraticOriginalSmallResidue F S₀ hζ M K g e) D u g‖ ≤ Cr * B := by
    have hb := hres M P K hM hP hK.le hKM D u g
      (fun b hb => ⟨hDsf b hb, (hDcols b hb).2.2⟩)
      (fun b hb c hc _ => hDclass b hb c hc)
    refine hb.trans ?_
    simpa only [B, Q, L, A, R, m, coeffMass, mul_assoc] using
      component_scale_mono Cr Q L (A + R) S m hCr.le (zero_le_one.trans hQ)
        (zero_le_one.trans hL) hm (by dsimp [S]; linarith)
  have hcomp := sourceQuadraticB3Block_re_le_component_norms F S₀ hζ hM0 hK.le
    (quadraticSmallErrorLine_pos hδ) (quadraticSmallErrorLine_lt_one δ)
    (quadraticDualErrorLine_pos hδ) (quadraticDualErrorLine_lt_one δ) D u g hDsf
  refine hcomp.trans ?_
  calc
    _ ≤ Cd * B + Ce * B + Ct * B + Cs * B + Cr * B :=
      add_le_add (add_le_add (add_le_add (add_le_add hd he) ht) hs) hr
    _ = _ := by dsimp [B, Q, L, S, A, R, m, D]; ring

end
end ArtinMatthews.SourceEulerAssembly
