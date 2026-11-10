module

public import ArtinMatthews.MarkedMajorScalarCharacterTerm
public import ArtinMatthews.MarkedMajorMellinEnergyAssembly
public import ArtinMatthews.MarkedMajorMellinLabelEnergyLog
public import ArtinMatthews.MarkedMajorMellinLabelEnergyParameters
public import ArtinMatthews.MarkedMajorScalarEndpointCentral
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

/-! Actual Mellin separation with the two conjugate long-frequency tests
and translated weighted means for the original arbitrary coefficients. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped ComplexConjugate ContDiff
noncomputable section

theorem markedMajorScalarMellin_all_log
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) (hηnorm : ∀ t,‖η t‖ ≤ 1)
    (hsupp : Function.support η ⊆ Set.Icc 1 4) (ψ : SchwartzMap ℝ ℂ)
    {Rψ : ℝ} (hψ : tsupport ψ ⊆ Set.Icc (-Rψ) Rψ)
    (c C₁ δ σ a Cα Cβ P Kx v₀ : ℝ)
    (hc : 0 < c) (hC₁ : 0 < C₁) (hδ : 0 < δ) (hσ : 0 ≤ σ) (ha : 0 ≤ a)
    (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ) (hP : 0 ≤ P) (hv₀ : 0 < v₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ L : ℝ in atTop,
      ∀ {J : Type} [Fintype J] [DecidableEq J] (P₀ : Finset ℕ) (bands : J → Finset ℕ),
        (∀ p ∈ P₀,p.Prime) → (∀ j p,p ∈ bands j → p.Prime) →
        (∀ j,Disjoint P₀ (bands j)) → Pairwise (fun i j => Disjoint (bands i) (bands j)) →
        v₀ ≤ bandReciprocalMass P₀ → (∀ j,0 < bandReciprocalMass (bands j)) →
        (∀ p ∈ P₀,c*L^(1/(10:ℝ)) ≤ Real.log p) →
        (∀ p ∈ P₀,Real.log p ≤ C₁*L^(1/(5:ℝ))) →
        ∀ (Y H U : ℝ) (S : Finset ℕ) (l r : ℕ) (α β : ℕ → ℂ),
          0 < Y → ∀ hH : 0 < H, ∀ hU : 0 < U, Real.exp (δ*L) ≤ U →
          1 ≤ H*U → H*U ≤ Real.exp (σ*L) → H*U ≤ Kx*Real.exp L →
          (∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
          (∀ m ∈ S,‖α m‖ ≤ L^Cα) → (∀ n ∈ Icc l r,‖β n‖ ≤ L^Cβ) →
          (∀ (k : ℕ) [NeZero k], (k:ℝ) ≤ L^a → ∀ χ : DirichletCharacter ℂ k,∀ t : ℝ,
            |t| ≤ 2*(H*U)*L^(a+2) → ‖markedTwistedSum S α χ t‖/H ≤ L^(-R)) →
          ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ L^a →
          ∀ (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ), |θ| ≤ 2*L^a →
          let X := H*U
          let allBands := fun j : Option J => j.elim P₀ bands
          let A := markedMajorScalarCharacterEndpoint allBands η q χ 1 2 3 θ Y H U S (Icc l r) α β
          let B := markedMajorScalarCharacterEndpoint allBands η q χ 0 4 5 (-θ) Y H U S (Icc l r)
            (fun m => conj (α m)) (fun n => conj (β n))
          (∫ p : ℝ×ℝ, ‖markedMajorConstructedCoefficient ψ
            (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<32) hψ (mul_pos hH hU) θ
            (p.1/X,p.2)*(A p.1*B (p.2-p.1))‖) ≤ L^(-P) := by
  let D := Cα+Cβ
  obtain ⟨n,hn⟩ := exists_nat_ge (P+2*a+2*D+9)
  obtain ⟨CF,hCF,hkernel⟩ := markedMajor_constructed_endpoint_L1_energy ψ
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<32) hψ n
  obtain ⟨CM,hCM,hmean⟩ := markedMajorScalarEndpoint_weighted_mean σ Cα Cβ hσ η hηnorm
    (by norm_num : (0:ℝ)≤4) (fun x hx => (hsupp hx).2)
  have hP' : 0 ≤ a+2+P+2 := by linarith
  obtain ⟨R,hR,hcentral⟩ := markedMajorScalarEndpoint_central η hη
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)≤4) hsupp
    c C₁ δ σ a Cα Cβ (a+2+P+2) Kx v₀ hc hC₁ hδ hσ ha hCα hCβ hP' hv₀
  refine ⟨R,hR,?_⟩
  filter_upwards [hcentral,hmean,
    markedMajorLabelEnergy_log_budget a D P 2 CF CM markedMajorFourierWeightMass
      hCF.le hCM.le markedMajorFourierWeightMass_nonneg n hn,eventually_ge_atTop (1:ℝ)]
    with L hcentral hmean hbudget hL
  intro J _ _ P₀ bands hP₀ hbands hdis₀ hdis hV₀ hV hlo hhi
    Y H U S l r α β hY hH hU hUlo hX hupper hcomp hS hl hr hα hβ hlong q _ hq χ θ hθ
  dsimp only
  let X := H*U
  let allBands := fun j : Option J => j.elim P₀ bands
  let T := Icc l r
  let χL := markedCoordinateDirichlet q χ 1
  let χR := markedCoordinateDirichlet q χ 0
  let αL := fun m => α m*markedCoordinateDirichlet q χ 2 m
  let βL := fun n => β n*markedCoordinateDirichlet q χ 3 n
  let αR := fun m => conj (α m)*markedCoordinateDirichlet q χ 4 m
  let βR := fun n => conj (β n)*markedCoordinateDirichlet q χ 5 n
  let A := markedMajorScalarEndpoint allBands η χL θ Y H U S T αL βL
  let B := markedMajorScalarEndpoint allBands η χR (-θ) Y H U S T αR βR
  have hXp : 0 < X := mul_pos hH hU
  have hT (n : ℕ) (hn : n∈T) : U ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*U :=
    ⟨hl.trans (Nat.cast_le.mpr (mem_Icc.mp hn).1),(Nat.cast_le.mpr (mem_Icc.mp hn).2).trans hr⟩
  have hcoeff (a : ℕ → ℂ) (k : Fin 6) (s : ℕ) :
      ‖a s*markedCoordinateDirichlet q χ k s‖ ≤ ‖a s‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((markedCoordinateDirichlet q χ k).norm_le_one _)
  have hαL (m : ℕ) (hm : m∈S) : ‖αL m‖ ≤ L^Cα := (hcoeff α 2 m).trans (hα m hm)
  have hβL (n : ℕ) (hn : n∈T) : ‖βL n‖ ≤ L^Cβ := (hcoeff β 3 n).trans (hβ n hn)
  have hαR (m : ℕ) (hm : m∈S) : ‖αR m‖ ≤ L^Cα := (hcoeff (fun n => conj (α n)) 4 m).trans
    (by simpa only [Complex.norm_conj] using hα m hm)
  have hβR (n : ℕ) (hn : n∈T) : ‖βR n‖ ≤ L^Cβ := (hcoeff (fun n => conj (β n)) 5 n).trans
    (by simpa only [Complex.norm_conj] using hβ n hn)
  let W := 1+|θ|
  have hW : 1 ≤ W := le_add_of_nonneg_right (abs_nonneg θ)
  have hWθ : W ≤ (1+2)*L^a := markedMajorLabelEnergy_theta_scale hL ha hθ
  have hθ' : |-θ| ≤ 2*L^a := by simpa only [abs_neg] using hθ
  let Z := 2*X*L^(a+2)
  have hlongL (t : ℝ) (ht : t ∈ Set.Icc (-Z) Z) :
      ‖markedMajorScalarPolynomial S H αL t‖ ≤ L^(-R) := by
    dsimp only [αL]
    rw [markedMajorScalarPolynomial_eq_twisted,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hH]
    exact hlong q hq (markedCoordinateDirichlet q χ 2) t (abs_le.mpr ht)
  have hlongR (t : ℝ) (ht : t ∈ Set.Icc (-Z) Z) :
      ‖markedMajorScalarPolynomial S H αR t‖ ≤ L^(-R) := by
    dsimp only [αR]
    rw [markedMajorScalarPolynomial_eq_twisted,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hH]
    have he := markedTwistedSum_norm_conjugate S α (star (markedCoordinateDirichlet q χ 4)) t
    rw [star_star] at he
    rw [he]
    exact hlong q hq (star (markedCoordinateDirichlet q χ 4)) (-t)
      (by simpa only [abs_neg] using abs_le.mpr ht)
  have hA := hcentral P₀ bands hP₀ hbands hdis₀ hdis hV₀ hV hlo hhi
    Y θ H U S l r αL βL hY hθ hH hUlo hX hupper hcomp hS hl hr hαL hβL hlongL q χL
  have hB := hcentral P₀ bands hP₀ hbands hdis₀ hdis hV₀ hV hlo hhi
    Y (-θ) H U S l r αR βR hY hθ' hH hUlo hX hupper hcomp hS hl hr hαR hβR hlongR q χR
  have hPall (j : Option J) (p : ℕ) (hp : p ∈ allBands j) : p.Prime := by
    cases j with
    | none => exact hP₀ p hp
    | some j => exact hbands j p hp
  have hdisall : Pairwise (fun i j => Disjoint (allBands i) (allBands j)) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hdis₀ _
    · exact (hdis₀ _).symm
    · exact hdis (fun h => hij (congrArg Option.some h))
  have hVall (j : Option J) : 0 < bandReciprocalMass (allBands j) := by
    cases j with
    | none => exact hv₀.trans_le hV₀
    | some j => exact hV j
  have hMA (s : ℝ) := hmean allBands hPall hdisall hVall Y θ H U S T αL βL
    hY hH hU hX hupper hS hT hαL hβL q χL W s hW
  have hMB (s : ℝ) := hmean allBands hPall hdisall hVall Y (-θ) H U S T αR βR
    hY hH hU hX hupper hS hT hαR hβR q χR W s hW
  have hK := hkernel X hX hXp θ (L^(a+2)) (L^(-(a+2+P+2))) (CM*W*L^(2*D+5))
    (Real.rpow_nonneg (zero_le_one.trans hL) _) A B
    (markedMajorScalarEndpoint_continuous allBands η χL θ Y H U S T αL βL)
    (markedMajorScalarEndpoint_continuous allBands η χR (-θ) Y H U S T αR βR)
    (markedMajorScalarEndpoint_bounded allBands η χL θ Y H U S T αL βL)
    (markedMajorScalarEndpoint_bounded allBands η χR (-θ) Y H U S T αR βR)
    hA hB hMA hMB
  exact hK.trans (hbudget W hW hWθ)

end
end ArtinMatthews
