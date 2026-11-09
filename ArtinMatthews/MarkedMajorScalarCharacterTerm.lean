module

public import ArtinMatthews.MarkedMajorScalarEndpointSource
public import ArtinMatthews.MarkedMajorMellinFiniteEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Exact factorization and normalized Mellin bound of a character term
from the original six-coordinate arc expansion. -/
namespace ArtinMatthews
open Finset MeasureTheory
open scoped ComplexConjugate
noncomputable section

variable {J : Type*} [Fintype J]

def markedMajorScalarCharacterEndpoint (P : J → Finset ℕ) (η : ℝ → ℂ)
    (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ) (i j k : Fin 6)
    (θ Y H U : ℝ) (S T : Finset ℕ) (α β : ℕ → ℂ) : ℝ → ℂ :=
  markedMajorScalarEndpoint P η (markedCoordinateDirichlet q χ i) θ Y H U S T
    (fun m => α m*markedCoordinateDirichlet q χ j m)
    (fun n => β n*markedCoordinateDirichlet q χ k n)

theorem markedMajorScalarArcCharacterTerm_norm_le (P : J → Finset ℕ) (η : ℝ → ℂ)
    (ψ : SchwartzMap ℝ ℂ) {R Y H U : ℝ} (hψ : tsupport ψ ⊆ Set.Icc (-R) R)
    (hY : 0 < Y) (hH : 0 < H) (hU : 0 < U) (hη : Function.support η ⊆ Set.Icc 1 4)
    (S T : Finset ℕ) (α β : ℕ → ℂ)
    (hS : ∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H)
    (hT : ∀ n ∈ T,U ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*U)
    (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ) :
    let X := H*U
    let A := markedMajorScalarCharacterEndpoint P η q χ 1 2 3 θ Y H U S T α β
    let B := markedMajorScalarCharacterEndpoint P η q χ 0 4 5 (-θ) Y H U S T
      (fun m => conj (α m)) (fun n => conj (β n))
    ‖(Y:ℂ)⁻¹*markedMajorArcCharacterTerm (markedMajorScalarTripleSet P Y S T)
      (markedMajorScalarTripleSet P Y S T) (markedMajorScalarBare P η Y α β)
      (markedMajorScalarBare P η Y (fun m => conj (α m)) (fun n => conj (β n))) ψ q χ θ Y‖ ≤
      (Y*X)*(∫ p : ℝ×ℝ, ‖markedMajorConstructedCoefficient ψ
        (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<32) hψ (mul_pos hH hU) θ
        (p.1/X,p.2)*(A p.1*B (p.2-p.1))‖) := by
  dsimp only
  let X := H*U
  let L := markedMajorScalarTripleSet P Y S T
  let v := fun z => markedMajorLabelTripleValue z/(Y*X)
  let a := fun m => α m*markedCoordinateDirichlet q χ 2 m
  let b := fun n => β n*markedCoordinateDirichlet q χ 3 n
  let a' := fun m => conj (α m)*markedCoordinateDirichlet q χ 4 m
  let b' := fun n => conj (β n)*markedCoordinateDirichlet q χ 5 n
  let C := markedMajorScalarTripleWeight P η (markedCoordinateDirichlet q χ 1) θ Y a b
  let C' := markedMajorScalarTripleWeight P η (markedCoordinateDirichlet q χ 0) (-θ) Y a' b'
  let A := markedMajorScalarEndpoint P η (markedCoordinateDirichlet q χ 1) θ Y H U S T a b
  let B := markedMajorScalarEndpoint P η (markedCoordinateDirichlet q χ 0) (-θ) Y H U S T a' b'
  have hX : 0 < X := mul_pos hH hU
  have hYX := mul_pos hY hX
  have hS₀ : ∀ m ∈ S,0 < m := fun m hm => Nat.cast_pos.mp (hH.trans_le (hS m hm).1)
  have hT₀ : ∀ n ∈ T,0 < n := fun n hn => Nat.cast_pos.mp (hU.trans_le (hT n hn).1)
  have hcompact : ∀ z ∈ L,v z ∈ Set.Icc (1/2:ℝ) 32 :=
    markedMajorScalarTripleSet_compact P Y H U S T hY hH hU hS hT
  have hv (z : ℕ×(ℕ×ℕ)) (hz : z∈L) : 0 < markedMajorLabelTripleValue z := by
    have hh : 0 < v z := (by norm_num : (0:ℝ)<1/2).trans_le (hcompact z hz).1
    exact (div_pos_iff_of_pos_right hYX).mp hh
  have hA := markedMajorScalarEndpoint_continuous P η (markedCoordinateDirichlet q χ 1) θ Y H U S T a b
  have hB := markedMajorScalarEndpoint_continuous P η (markedCoordinateDirichlet q χ 0) (-θ) Y H U S T a' b'
  have hAb := markedMajorScalarEndpoint_bounded P η (markedCoordinateDirichlet q χ 1) θ Y H U S T a b
  have hBb := markedMajorScalarEndpoint_bounded P η (markedCoordinateDirichlet q χ 0) (-θ) Y H U S T a' b'
  have hAn (t : ℝ) : ‖markedMajorEndpointPolynomial L C v t‖ ≤ (Y*X)*‖A t‖ :=
    (markedMajor_scaled_polynomial_norm L C markedMajorLabelTripleValue hv hYX A
      (markedMajorScalarEndpoint_source P η _ θ Y H U S T a b hY hH hU hη hS₀ hT₀) t).le
  have hBn (t : ℝ) : ‖markedMajorEndpointPolynomial L C' v t‖ ≤ (Y*X)*‖B t‖ :=
    (markedMajor_scaled_polynomial_norm L C' markedMajorLabelTripleValue hv hYX B
      (markedMajorScalarEndpoint_source P η _ (-θ) Y H U S T a' b' hY hH hU hη hS₀ hT₀) t).le
  have hsum :
      markedMajorArcCharacterTerm L L (markedMajorScalarBare P η Y α β)
        (markedMajorScalarBare P η Y (fun m => conj (α m)) (fun n => conj (β n))) ψ q χ θ Y =
      ∑ z ∈ L,∑ z' ∈ L,(C z*C' z')*(ψ (X*(v z-v z'))*
        OAI.Problem337.RealPhase.phase (θ*(X*(v z-v z')))) := by
    unfold markedMajorArcCharacterTerm
    apply sum_congr rfl
    intro z _
    apply sum_congr rfl
    intro z' _
    have hscale : X*(v z-v z') = (markedMajorLabelTripleValue z-markedMajorLabelTripleValue z')/Y := by
      dsimp only [v]
      field_simp [hX.ne',hY.ne']
    simp only [markedMajorIntegerDeterminant_real,hscale,mul_div_assoc]
    dsimp only [C,C',a,b,a',b',markedMajorScalarBare,markedMajorScalarTripleWeight,markedMajorLabelWeight,
      markedMajorLabelArcPhase,markedMajorCharacterLeft,markedMajorCharacterRight]
    ring
  rw [hsum]
  apply markedMajor_normalized_endpoint_bound hX hY
  exact markedMajor_finite_endpoint_L1_bound L L C C' v v ψ (by norm_num) (by norm_num)
    hψ hX hYX.le θ hcompact hcompact A B hA hB hAb hBb hAn hBn

end
end ArtinMatthews
