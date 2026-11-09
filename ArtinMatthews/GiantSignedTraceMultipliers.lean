module

public import ArtinMatthews.GiantSignedTraceProjection


set_option backward.privateInPublic true
@[expose] public section

/-! Local multipliers change coefficients without changing any move or target.
The projected word therefore uses the same chronological trace. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

universe u v
variable {X : Type u}

def giantSignedTraceMultiplyRow (r : GiantSignedTraceRow.{u,v} X)
    (φ : (x : X) → r.Move x → ℂ) : GiantSignedTraceRow.{u,v} X :=
  { r with coefficient := fun x m => r.coefficient x m * φ x m }

def GiantSignedTraceMultipliers : List (GiantSignedTraceRow.{u,v} X) → Type (max u v)
  | [] => PUnit
  | r :: rs => ((x : X) → r.Move x → ℂ) × GiantSignedTraceMultipliers rs

def giantSignedTraceMultiplyRows :
    (rs : List (GiantSignedTraceRow.{u,v} X)) → GiantSignedTraceMultipliers rs →
      List (GiantSignedTraceRow.{u,v} X)
  | [], _ => []
  | r :: rs, φ => giantSignedTraceMultiplyRow r φ.1 :: giantSignedTraceMultiplyRows rs φ.2

def giantSignedTraceMultipliersProduct :
    (rs : List (GiantSignedTraceRow.{u,v} X)) → GiantSignedTraceMultipliers rs →
      (x : X) → GiantSignedTrace rs x → ℂ
  | [], _, _, _ => 1
  | r :: rs, φ, x, ⟨m,t⟩ => φ.1 x m * giantSignedTraceMultipliersProduct rs φ.2 (r.target x m) t

def GiantSignedTraceMultipliersBounded :
    (rs : List (GiantSignedTraceRow.{u,v} X)) → GiantSignedTraceMultipliers rs → Prop
  | [], _ => True
  | r :: rs, φ => (∀ x (m : r.Move x), ‖φ.1 x m‖ ≤ 1) ∧ GiantSignedTraceMultipliersBounded rs φ.2

def giantSignedTraceMultiplyEquiv :
    (rs : List (GiantSignedTraceRow.{u,v} X)) → (φ : GiantSignedTraceMultipliers rs) →
      (x : X) → GiantSignedTrace rs x ≃ GiantSignedTrace (giantSignedTraceMultiplyRows rs φ) x
  | [], _, _ => Equiv.refl _
  | r :: rs, φ, x => Equiv.sigmaCongrRight (fun m : r.Move x =>
      giantSignedTraceMultiplyEquiv rs φ.2 (r.target x m))

theorem giantSignedTraceMultiplyWeight (f : X → ℂ) (rs : List (GiantSignedTraceRow.{u,v} X))
    (φ : GiantSignedTraceMultipliers rs) (x : X) (t : GiantSignedTrace rs x) :
    giantSignedTraceWeight f (giantSignedTraceMultiplyRows rs φ) x (giantSignedTraceMultiplyEquiv rs φ x t) =
      giantSignedTraceWeight f rs x t * giantSignedTraceMultipliersProduct rs φ x t := by
  induction rs generalizing x with
  | nil => exact (mul_one (f x)).symm
  | cons r rs ih =>
      obtain ⟨m,t⟩ := t
      change (r.coefficient x m * φ.1 x m) *
        giantSignedTraceWeight f (giantSignedTraceMultiplyRows rs φ.2) (r.target x m)
          (giantSignedTraceMultiplyEquiv rs φ.2 (r.target x m) t) =
        (r.coefficient x m * giantSignedTraceWeight f rs (r.target x m) t) *
          (φ.1 x m * giantSignedTraceMultipliersProduct rs φ.2 (r.target x m) t)
      rw [ih]
      ac_rfl

theorem giantSignedTraceMultiplyWithin (good : X → Prop) (rs : List (GiantSignedTraceRow.{u,v} X))
    (φ : GiantSignedTraceMultipliers rs) (x : X) (t : GiantSignedTrace rs x) :
    GiantSignedTraceWithin good (giantSignedTraceMultiplyRows rs φ) x (giantSignedTraceMultiplyEquiv rs φ x t) ↔
      GiantSignedTraceWithin good rs x t := by
  induction rs generalizing x with
  | nil => rfl
  | cons r rs ih =>
      obtain ⟨m,t⟩ := t
      change (good x ∧ good (r.target x m) ∧
        GiantSignedTraceWithin good (giantSignedTraceMultiplyRows rs φ.2) (r.target x m)
          (giantSignedTraceMultiplyEquiv rs φ.2 (r.target x m) t)) ↔
        (good x ∧ good (r.target x m) ∧ GiantSignedTraceWithin good rs (r.target x m) t)
      rw [ih]

theorem giantSignedTraceMultiplyRow_absolute (degree : X → ℕ) (r : GiantSignedTraceRow.{u,v} X)
    (hr : GiantSignedTraceRowAbsolute degree r) (φ : (x : X) → r.Move x → ℂ)
    (hφ : ∀ x m, ‖φ x m‖ ≤ 1) :
    GiantSignedTraceRowAbsolute degree (giantSignedTraceMultiplyRow r φ) := by
  intro f hf hF
  obtain ⟨hs, U, v, hU, hv, he⟩ := hr f hf hF
  let a (x : X) (m : r.Move x) := ‖r.coefficient x m‖ * f (r.target x m)
  let b (x : X) (m : r.Move x) := ‖r.coefficient x m * φ x m‖ * f (r.target x m)
  have hb (x : X) (m : r.Move x) : b x m ≤ a x m := by
    simp only [a, b, norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (hφ x m)) (hf _)
  have hs' (x : X) : Summable (b x) :=
    (hs x).of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (hf _)) (hb x)
  refine ⟨hs', U, v, hU, hv, fun x => ?_⟩
  exact ((hs' x).tsum_le_tsum (hb x) (hs x)).trans (he x)

theorem giantSignedTraceMultiplyRows_absolute (degree : X → ℕ) (rs : List (GiantSignedTraceRow.{u,v} X))
    (hr : ∀ r ∈ rs, GiantSignedTraceRowAbsolute degree r)
    (φ : GiantSignedTraceMultipliers rs) (hφ : GiantSignedTraceMultipliersBounded rs φ) :
    ∀ r ∈ giantSignedTraceMultiplyRows rs φ, GiantSignedTraceRowAbsolute degree r := by
  induction rs with
  | nil => simp [giantSignedTraceMultiplyRows]
  | cons r rs ih =>
      intro a ha
      change a ∈ giantSignedTraceMultiplyRow r φ.1 :: giantSignedTraceMultiplyRows rs φ.2 at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact giantSignedTraceMultiplyRow_absolute degree r (hr r List.mem_cons_self) φ.1 hφ.1
      · exact ih (fun b hb => hr b (List.mem_cons_of_mem _ hb)) φ.2 hφ.2 a ha

theorem giantSignedTraceMultiplyProjectedWord_eq (degree : X → ℕ) (f : X → ℂ)
    (hf : GiantSignedTraceExponential degree (fun x => ‖f x‖))
    (rs : List (GiantSignedTraceRow.{u,v} X)) (hr : ∀ r ∈ rs, GiantSignedTraceRowAbsolute degree r)
    (φ : GiantSignedTraceMultipliers rs) (hφ : GiantSignedTraceMultipliersBounded rs φ)
    (good : X → Prop) (x : X) :
    giantSignedTraceProjectedWord good (giantSignedTraceMultiplyRows rs φ) f x =
      ∑' t : GiantSignedTrace rs x, if GiantSignedTraceWithin good rs x t then
        giantSignedTraceWeight f rs x t * giantSignedTraceMultipliersProduct rs φ x t else 0 := by
  rw [giantSignedTraceProjectedWord_eq degree f hf _
    (giantSignedTraceMultiplyRows_absolute degree rs hr φ hφ)]
  let e := giantSignedTraceMultiplyEquiv rs φ x
  refine (e.tsum_eq _).symm.trans (tsum_congr (fun t => ?_))
  dsimp only [e]
  rw [giantSignedTraceMultiplyWeight, giantSignedTraceMultiplyWithin]

end
end ArtinMatthews
