module

public import ArtinMatthews.SourceKPTameOperator
public import ArtinMatthews.SourceKPTameHilbertPhase
public import ArtinMatthews.SourceFiniteKPProjectiveTorus


set_option backward.privateInPublic true
@[expose] public section

/-! The literal three-dimensional Weyl-conjugate torus representation
on the actual local covering torus. Its norm factor is Q^(ord(y)/6)
and its central action is the selected cubic embedding. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups ValuativeRel
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (π : (P.adicCompletion K)ˣ)
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ))

def sourceKPTameTorusRepresentation :
    Representation ℂ (SourceFiniteKPRankOneTorus K hζ P) (ZMod 3 → ℂ) where
  toFun x :=
    let ν := sourceKPFiniteVal K P
    let y := sourceFiniteKPRankOneBase K hζ P x
    sourceKPTameOperator (Ideal.absNorm P.asIdeal : ℝ) (sourceKPCentralComplex K hζ P x.val.central)
      (sourceKPTameUniformizerCharacter K hζ P π (sourceKPUnitPart ν π y)) (sourceKPValuationOrder ν y)
  map_one' := by
    let ν := sourceKPFiniteVal K P
    let b := sourceFiniteKPRankOneBase K hζ P
    let e := sourceKPCentralComplex K hζ P
    let r := sourceKPTameUniformizerCharacter K hζ P π
    change sourceKPTameOperator (Ideal.absNorm P.asIdeal : ℝ) (e 1)
      (r (sourceKPUnitPart ν π (b 1))) (sourceKPValuationOrder ν (b 1)) = 1
    rw [map_one b, map_one e, sourceKPValuationOrder_one,
      sourceKPUnitPart_of_unit ν π 1 (map_one ν), map_one r, sourceKPTameOperator_one]
  map_mul' x y := by
    let ν := sourceKPFiniteVal K P
    let b := sourceFiniteKPRankOneBase K hζ P
    let e := sourceKPCentralComplex K hζ P
    let r := sourceKPTameUniformizerCharacter K hζ P π
    let Q : ℝ := Ideal.absNorm P.asIdeal
    let j := sourceKPValuationOrder ν (b x)
    let k := sourceKPValuationOrder ν (b y)
    let u := r (sourceKPUnitPart ν π (b x))
    let v := r (sourceKPUnitPart ν π (b y))
    change sourceKPTameOperator Q (e (x * y).val.central)
        (r (sourceKPUnitPart ν π (b (x * y)))) (sourceKPValuationOrder ν (b (x * y))) =
      sourceKPTameOperator Q (e x.val.central) u j * sourceKPTameOperator Q (e y.val.central) v k
    have hQ : 0 < Q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot))
    have hu : u ^ 3 = 1 := sourceKPTameUniformizerCharacter_cube K hζ P π _
    have hv : v ^ 3 = 1 := sourceKPTameUniformizerCharacter_cube K hζ P π _
    have hC : e (x * y).val.central = e x.val.central * e y.val.central * (v ^ j * u ^ (-k)) := by
      rw [sourceFiniteKPRankOne_mul_central, map_mul e, map_mul e]
      exact congrArg (e x.val.central * e y.val.central * ·)
        (sourceKPTameHilbert_phase K hζ P h6 π hπ (b x) (b y))
    have hU : r (sourceKPUnitPart ν π (b (x * y))) = u * v := by
      rw [map_mul b, sourceKPUnitPart_mul, map_mul r]
    have hJ : sourceKPValuationOrder ν (b (x * y)) = j + k := by
      rw [map_mul b, sourceKPValuationOrder_mul]
    have hphaseU : sourceKPCubicPower u (-(k : ZMod 3)) = u ^ (-k) := by
      calc
        _ = sourceKPCubicPower u ((-k : ℤ) : ZMod 3) :=
          congrArg (sourceKPCubicPower u) (Int.cast_neg (R := ZMod 3) k).symm
        _ = _ := sourceKPCubicPower_int u hu (-k)
    have hphaseV := sourceKPCubicPower_int v hv j
    rw [hC, hU, hJ, ← hphaseU, ← hphaseV]
    simpa only [mul_assoc] using sourceKPTameOperator_mul Q hQ (e x.val.central) (e y.val.central) u v hu hv j k

def sourceKPTameProjectiveTorusRepresentation :
    Representation ℂ (SourceFiniteKPProjectiveTorus K hζ P) (ZMod 3 → ℂ) :=
  (sourceKPTameTorusRepresentation K hζ P h6 π hπ).comp
    (sourceFiniteKPProjectiveTorusEquiv K hζ P).symm.toMonoidHom

theorem sourceKPTameProjectiveTorusRepresentation_of_rankOne (x : SourceFiniteKPRankOneTorus K hζ P) :
    sourceKPTameProjectiveTorusRepresentation K hζ P h6 π hπ (sourceFiniteKPRankOneToProjective K hζ P x) =
      sourceKPTameTorusRepresentation K hζ P h6 π hπ x := by
  let e := sourceFiniteKPProjectiveTorusEquiv K hζ P
  change sourceKPTameTorusRepresentation K hζ P h6 π hπ (e.symm (e x)) = _
  rw [MulEquiv.symm_apply_apply]

end
end ArtinMatthews
