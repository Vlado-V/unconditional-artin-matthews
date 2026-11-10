module

public import ArtinMatthews.SourceQuadraticSmallAmplitude
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

/-- The original Small amplitude is bounded on the entire squarefree row ball. -/
theorem sourceQuadraticOriginalSmallAmplitude_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ K P : ℝ, 1 ≤ K → 1 ≤ P → ∀ cols : Finset E,
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ 2 * P) →
      (∀ b ∈ cols, ∀ c ∈ cols,
        sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) →
      ∀ (u : E → ℂ) (g : E), (q g : ℝ) ≤ 2 * P → ∀ s : ℂ, 0 ≤ s.re →
      ‖sourceQuadraticOriginalSmallAmplitude F S₀ hζ K cols u g s‖ ≤
        C * (K * P) ^ η * (2 * P) ^ (2 * η) * (P + K ^ α) * coeffMass cols u := by
  obtain ⟨Cb, hCb, hb⟩ := sourceQuadraticSmallEulerRowSum_bound F S₀ hζ htrace hE η hη
  obtain ⟨Ce, hCe, he⟩ := quadraticSmallEuler_subpower F η hη
  let N : ℝ := (sourceQuadraticBlockBadIdeal F S₀).absNorm
  let A := Ce * (1 + N ^ η)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A * Cb, by positivity, ?_⟩
  intro K P hK hP cols hcols hclass u g hg s hs
  have hmass0 : 0 ≤ coeffMass cols u := coeffMass_nonneg _ _
  let R := sourceQuadraticSmallResidualColumns F S₀ cols g
  let v := sourceQuadraticSmallResidualCoeff F S₀ g u
  have hrows (a : E) (ha : a ∈ sourceQuadraticSmallRows F S₀ K g) :
      sourceReflectionIsSquarefree a ∧ (q a : ℝ) ≤ K := by
    obtain ⟨hn, hsf, _⟩ := (sourceQuadraticSmallRows_mem F S₀ (by linarith) g a).mp ha
    exact ⟨hsf, hn⟩
  have hR (b : E) (hb' : b ∈ R) : sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ 2 * P :=
    ⟨sourceQuadraticSmallResidualColumns_squarefree F S₀ cols g (fun c hc => (hcols c hc).1) b hb',
      sourceQuadraticSmallResidualColumns_norm F S₀ cols g (2 * P) (fun c hc => (hcols c hc).2) b hb'⟩
  have hr := hb K P hK hP (sourceQuadraticSmallRows F S₀ K g) R hrows hR v s hs
  have hmass := sourceQuadraticSmallResidualCoeff_mass F S₀ cols g u
  have hr' : ‖sourceQuadraticSmallEulerRowSum F S₀ hζ
      (sourceQuadraticSmallRows F S₀ K g) R v s‖ ≤
        Cb * (K * P) ^ η * (2 * P) ^ η * (P + K ^ α) * coeffMass cols u :=
    hr.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
  have hf : ‖quadraticSmallEuler F (sourceQuadraticBlockModulus F S₀ g) s‖ ≤
      A * (2 * P) ^ η := by
    have h := he (sourceQuadraticBlockModulus F S₀ g)
      (sourceQuadraticBlockModulus_ne_bot F S₀ g) s hs
    rw [sourceQuadraticBlockModulus, map_mul, Nat.cast_mul, sourcePrimeExponentIdeal_norm,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at h
    calc
      _ ≤ Ce * (N ^ η * (q g : ℝ) ^ η) := h
      _ ≤ Ce * (N ^ η * (2 * P) ^ η) := by
        gcongr
      _ ≤ A * (2 * P) ^ η := by
        dsimp only [A]
        have hn : 0 ≤ N ^ η := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hp : 0 ≤ (2 * P) ^ η := by positivity
        nlinarith
  rw [sourceQuadraticOriginalSmallAmplitude_separate F S₀ hζ K cols
    (fun b hb' => (hcols b hb').1) hclass u g s, norm_mul]
  calc
    _ ≤ (A * (2 * P) ^ η) *
        (Cb * (K * P) ^ η * (2 * P) ^ η * (P + K ^ α) * coeffMass cols u) :=
      mul_le_mul hf hr' (norm_nonneg _) (by positivity)
    _ = (A * Cb) * (K * P) ^ η * ((2 * P) ^ η * (2 * P) ^ η) *
        (P + K ^ α) * coeffMass cols u := by ring
    _ = _ := by
      rw [← Real.rpow_add (by linarith : 0 < 2 * P)]
      congr 4
      ring

omit [IsTotallyComplex F] in
/-- Membership in the actual common-ideal set supplies the needed norm bound. -/
theorem sourceQuadraticSmallCommon_norm (P : ℝ) (cols : Finset E)
    (hcols : ∀ b ∈ cols, (q b : ℝ) ≤ 2 * P) (g : E)
    (hg : g ∈ sourceQuadraticCommonIdeals F S₀ cols) : (q g : ℝ) ≤ 2 * P := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hg
  have hn := sourceReflectionExteriorNorm_mono F S₀ (show p.1 ⊓ p.2 ≤ p.1 from inf_le_left)
  have hn' : (q (p.1 ⊓ p.2) : ℝ) ≤ q p.1 := by exact_mod_cast hn
  exact hn'.trans (hcols p.1 (Finset.mem_product.mp hp).1)

end
end ArtinMatthews.SourceEulerAssembly
