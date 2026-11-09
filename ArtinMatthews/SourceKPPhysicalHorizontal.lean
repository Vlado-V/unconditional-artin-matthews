module

public import ArtinMatthews.SourceKPReflectionHorizontalProduct
public import ArtinMatthews.SourceSLocalFiniteWeyl
public import ArtinMatthews.SourceKPAdelicCompactIntersection


set_option backward.privateInPublic true
@[expose] public section

/-! The signed reflection of the actual horizontal profile on the
whole S-local multiplicative group, with its literal finite cover phase. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Classical ContDiff BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "V" => InfinitePlace K
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Ω" => productUpper V
local notation "R" => sourceKPAdelicProjectiveRationalLift K hζ
local notation "D" => sourceKPAdelicProjectiveDiagonalLift K hζ
local notation "Ds" => sourceSLocalProjectiveDiagonalLift K S hζ
local notation "C" => sourceKPFiniteAdeleProjectiveCenter K hζ

def sourceKPSLocalReflectionArgument (b : Kˣ) : SWholeUnits K S :=
  sWholeDiagonal K S ((b⁻¹)^2)

def sourceKPSLocalHeight (x : SWholeUnits K S) (v : V) : ℝ :=
  ‖(x.1 v : v.Completion)‖

theorem sourceKPSLocalHeight_pos (x : SWholeUnits K S) (v : V) :
    0 < sourceKPSLocalHeight K S x v :=
  norm_pos_iff.mpr (x.1 v).ne_zero

private theorem reflectionArgument_arch_norm (b : Kˣ) (v : V) :
    sourceKPSLocalHeight K S (sourceKPSLocalReflectionArgument K S b) v =
      (‖(sourceKPCuspRationalComplexUnit K hζ b v : ℂ)‖ ^ 2)⁻¹ := by
  let β : Kˣ →* v.Completionˣ := Units.map (algebraMap K v.Completion).toMonoidHom
  change ‖(β ((b⁻¹)^2) : v.Completion)‖ = _
  have hβ : (sourceKPCuspRationalComplexUnit K hζ b v : ℂ) =
      sourceKPArchComplexEquiv K hζ v (β b : v.Completion) := rfl
  rw [map_pow β,map_inv β,Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val,norm_pow,norm_inv,
    hβ,sourceKPArchComplexEquiv_norm,inv_pow]

theorem sourceKPSLocalHeight_reflection (b : Kˣ) (x : SWholeUnits K S) :
    sourceKPReflectionHeight K hζ b (sourceKPSLocalHeight K S x) =
      sourceKPSLocalHeight K S (sourceKPSLocalReflectionArgument K S b * x⁻¹) := by
  funext v
  let a := sourceKPSLocalReflectionArgument K S b
  have ha : sourceKPSLocalHeight K S (a*x⁻¹) v =
      sourceKPSLocalHeight K S a v * (sourceKPSLocalHeight K S x v)⁻¹ := by
    change ‖((a*x⁻¹).1 v : v.Completion)‖ =
      ‖(a.1 v : v.Completion)‖ * ‖(x.1 v : v.Completion)‖⁻¹
    have he : (a*x⁻¹).1 v = a.1 v * (x.1 v)⁻¹ := rfl
    rw [he,Units.val_mul,Units.val_inv_eq_inv_val,norm_mul,norm_inv]
  rw [ha,reflectionArgument_arch_norm K hζ S b v]
  unfold sourceKPReflectionHeight
  rw [mul_inv_rev,mul_comm]

def sourceKPPhysicalHorizontalValue (ε : V → Bool) (l : List V)
    (W : Y → ℂ) (qf : Gf) (x : SWholeUnits K S) : ℂ :=
  sourceProductHorizontalList ε l
    (sourceKPCompactChartPullback K hζ W (QuotientGroup.mk ((Ds x).2*qf)))
    (sourceKPCuspHeightPoint K (sourceKPSLocalHeight K S x))

def sourceKPReflectedHorizontalFiber (b : Kˣ) (qf : Gf) (x : SWholeUnits K S) : Gf :=
  C (sourceSLocalWeylPhase K S hζ b (sourceKPSLocalReflectionArgument K S b*x⁻¹)) *
    (D (sourceSLocalExteriorIdele K S ((b⁻¹)^2))).2 * (Ds x).2 *
    (R (sourceKPReflectionWeyl K 1)).2 * qf

def sourceKPReflectedHorizontalValue (b : Kˣ) (ε : V → Bool) (l : List V)
    (W : Y → ℂ) (qf : Gf) (x : SWholeUnits K S) : ℂ :=
  sourceProductHorizontalList (fun v => !(ε v)) l
    (sourceKPCompactChartPullback K hζ W
      (QuotientGroup.mk (sourceKPReflectedHorizontalFiber K hζ S b qf x)))
    (sourceKPCuspHeightPoint K (sourceKPSLocalHeight K S x))

def sourceKPReflectionProductPhase (b : Kˣ) (ε : V → Bool) (l : List V) : ℂ :=
  (l.map (fun v => sourceKPReflectionHorizontalPhase K hζ b (ε v) v)).prod

theorem sourceKPReflectionProductPhase_norm (b : Kˣ) (ε : V → Bool) (l : List V) :
    ‖sourceKPReflectionProductPhase K hζ b ε l‖ = 1 := by
  induction l with
  | nil => simp [sourceKPReflectionProductPhase]
  | cons v l ih =>
    change ‖sourceKPReflectionHorizontalPhase K hζ b (ε v) v *
      sourceKPReflectionProductPhase K hζ b ε l‖ = 1
    rw [norm_mul,sourceKPReflectionHorizontalPhase_norm,ih,one_mul]

theorem sourceKPSLocalReflectionArgument_involution (b : Kˣ) (x : SWholeUnits K S) :
    sourceKPSLocalReflectionArgument K S b * (sourceKPSLocalReflectionArgument K S b*x⁻¹)⁻¹ = x := by
  rw [mul_inv_rev,inv_inv,mul_comm x,mul_inv_cancel_left]

theorem sourceKPPhysicalHorizontalValue_reflection (b : Kˣ) (ε : V → Bool) (l : List V)
    (hl : l.Nodup) (W : Y → ℂ)
    (hW : ∀ qf, ContDiffOn ℝ (∞ : ℕ∞ω) (sourceKPCompactChartPullback K hζ W qf) Ω)
    (qf : Gf) (x : SWholeUnits K S) :
    sourceKPPhysicalHorizontalValue K hζ S ε l W qf x =
      sourceKPReflectionProductPhase K hζ b ε l * sourceKPReflectedHorizontalValue K hζ S b ε l W qf
        (sourceKPSLocalReflectionArgument K S b*x⁻¹) := by
  let γ := sourceKPReflectionWeyl K b
  let a := sourceKPSLocalReflectionArgument K S b
  let y := sourceKPSLocalHeight K S x
  let g := (Ds x).2*qf
  let bg : SourceKPFiniteLevelFiber K hζ := QuotientGroup.mk g
  have h := sourceKPReflectionHorizontalList_quotient K hζ b ε l hl bg W (hW _) y
    (sourceKPSLocalHeight_pos K S x)
  have he : γ • bg = QuotientGroup.mk (sourceKPReflectedHorizontalFiber K hζ S b qf (a*x⁻¹)) := by
    change QuotientGroup.mk ((R γ).2*((Ds x).2*qf)) =
      QuotientGroup.mk (sourceKPReflectedHorizontalFiber K hζ S b qf (a*x⁻¹))
    apply congrArg QuotientGroup.mk
    rw [← mul_assoc,sourceSLocalFiniteWeyl_diagonal K S hζ b x,sourceKPReflectedHorizontalFiber]
    rw [show sourceKPSLocalReflectionArgument K S b*(a*x⁻¹)⁻¹ = x from
      sourceKPSLocalReflectionArgument_involution K S b x]
    rfl
  rw [he,sourceKPSLocalHeight_reflection K hζ S b x] at h
  exact h

end
end ArtinMatthews
