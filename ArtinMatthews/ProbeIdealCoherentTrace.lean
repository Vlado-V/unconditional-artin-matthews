module

public import ArtinMatthews.ProbeIdealPowerQuotients
public import ArtinMatthews.ProbePrimitiveCharacterShift
public import ArtinMatthews.VaryingKummerAnalyticIdealGaussFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Coherent primitive trace characters on powers of every nonzero prime
ideal.  Each step adjusts an actual trace-dual character by a proved unit
shift; compatibility is constructed, not postulated. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probeIdealReferenceTrace (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    AddChar ((𝓞 K) ⧸ P.asIdeal ^ n) ℂ :=
  idealTraceAddChar K (P.asIdeal ^ n) (pow_ne_zero n P.ne_bot)

theorem probeIdealReferenceTrace_primitive (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (probeIdealReferenceTrace K P n).IsPrimitive :=
  idealTraceAddChar_isPrimitive K (P.asIdeal ^ n) (pow_ne_zero n P.ne_bot)

abbrev ProbeIdealPrimitiveTrace (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :=
  {ψ : AddChar ((𝓞 K) ⧸ P.asIdeal ^ n) ℂ // ψ.IsPrimitive}

def probeIdealExtendTrace (P : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (c : ProbeIdealPrimitiveTrace K P (n + 1)) :
    {d : ProbeIdealPrimitiveTrace K P (n + 2) //
      probePrimePowerLowerChar P (n + 1) 1 d.val = c.val} := by
  let ψ := probeIdealReferenceTrace K P (n + 2)
  have hψ := probeIdealReferenceTrace_primitive K P (n + 2)
  let θ := probePrimePowerLowerChar P (n + 1) 1 ψ
  have hθ : θ.IsPrimitive := probePrimePowerLowerChar_primitive P (n + 1) 1 ψ hψ
  let : Finite ((𝓞 K) ⧸ P.asIdeal ^ (n + 1)) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero (n + 1) P.ne_bot)
  let : Fintype ((𝓞 K) ⧸ P.asIdeal ^ (n + 1)) := Fintype.ofFinite _
  let huData := probe_addChar_exists_unit_shift θ c.val hθ c.property
  let u := huData.choose
  have hu : θ.mulShift (u : (𝓞 K) ⧸ P.asIdeal ^ (n + 1)) = c.val := huData.choose_spec
  let a : 𝓞 K := Quotient.out (u : (𝓞 K) ⧸ P.asIdeal ^ (n + 1))
  have ha : Ideal.Quotient.mk (P.asIdeal ^ (n + 1)) a = (u : (𝓞 K) ⧸ P.asIdeal ^ (n + 1)) :=
    Ideal.Quotient.mk_out _
  have hna : a ∉ P.asIdeal := by
    apply (Ideal.Quotient.isUnit_mk_pow_iff_notMem P.asIdeal (Nat.succ_ne_zero n)).mp
    rw [ha]
    exact u.isUnit
  have hunit : IsUnit (Ideal.Quotient.mk (P.asIdeal ^ (n + 2)) a) :=
    Ideal.Quotient.isUnit_mk_pow_of_notMem P.asIdeal hna
  let U : ((𝓞 K) ⧸ P.asIdeal ^ (n + 2))ˣ := hunit.unit
  refine ⟨⟨ψ.mulShift (U : (𝓞 K) ⧸ P.asIdeal ^ (n + 2)),
    probe_addChar_primitive_unit_shift ψ hψ U⟩, ?_⟩
  change probePrimePowerLowerChar P (n + 1) 1 (ψ.mulShift (U : _)) = c.val
  calc
    _ = θ.mulShift (u : (𝓞 K) ⧸ P.asIdeal ^ (n + 1)) := by
      ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change ψ ((U : (𝓞 K) ⧸ P.asIdeal ^ (n + 2)) *
        Ideal.Quotient.mk (P.asIdeal ^ (n + 2)) (probeIdealUniformizer P ^ 1 * x)) =
        θ ((u : (𝓞 K) ⧸ P.asIdeal ^ (n + 1)) *
          Ideal.Quotient.mk (P.asIdeal ^ (n + 1)) x)
      rw [hunit.unit_spec, ← ha, ← map_mul (Ideal.Quotient.mk (P.asIdeal ^ (n + 1))) a x]
      change ψ ((Ideal.Quotient.mk _ a) *
        (Ideal.Quotient.mk _ (probeIdealUniformizer P ^ 1 * x))) =
        probePrimePowerLowerChar P (n + 1) 1 ψ (Ideal.Quotient.mk _ (a * x))
      rw [probePrimePowerLowerChar_mk, ← map_mul]
      congr 2
      ring
    _ = c.val := hu

def probeIdealTraceData (P : HeightOneSpectrum (𝓞 K)) :
    (n : ℕ) → ProbeIdealPrimitiveTrace K P n
  | 0 => ⟨probeIdealReferenceTrace K P 0, probeIdealReferenceTrace_primitive K P 0⟩
  | 1 => ⟨probeIdealReferenceTrace K P 1, probeIdealReferenceTrace_primitive K P 1⟩
  | n + 2 => (probeIdealExtendTrace K P n (probeIdealTraceData P (n + 1))).val

def probeIdealCoherentTrace (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    AddChar ((𝓞 K) ⧸ P.asIdeal ^ n) ℂ := (probeIdealTraceData K P n).val

theorem probeIdealCoherentTrace_primitive (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (probeIdealCoherentTrace K P n).IsPrimitive := (probeIdealTraceData K P n).property

theorem probeIdealCoherentTrace_first (P : HeightOneSpectrum (𝓞 K)) :
    probeIdealCoherentTrace K P 1 = probeIdealReferenceTrace K P 1 := rfl

theorem probeIdealCoherentTrace_step (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    probePrimePowerLowerChar P n 1 (probeIdealCoherentTrace K P (n + 1)) =
      probeIdealCoherentTrace K P n := by
  cases n with
  | zero =>
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx : Ideal.Quotient.mk (P.asIdeal ^ 0) x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (by simp)
    rw [hx, AddChar.map_zero_eq_one, AddChar.map_zero_eq_one]
  | succ n =>
    change probePrimePowerLowerChar P (n + 1) 1
      (probeIdealExtendTrace K P n (probeIdealTraceData K P (n + 1))).val.val =
        (probeIdealTraceData K P (n + 1)).val
    exact (probeIdealExtendTrace K P n (probeIdealTraceData K P (n + 1))).property

theorem probeIdealCoherentTrace_step_mk (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) (x : 𝓞 K) :
    probeIdealCoherentTrace K P (n + 1)
      (Ideal.Quotient.mk _ (probeIdealUniformizer P * x)) =
        probeIdealCoherentTrace K P n (Ideal.Quotient.mk _ x) := by
  have h := congrArg (fun ψ : AddChar ((𝓞 K) ⧸ P.asIdeal ^ n) ℂ =>
    ψ (Ideal.Quotient.mk _ x)) (probeIdealCoherentTrace_step K P n)
  simpa only [probePrimePowerLowerChar_mk, pow_one] using h

theorem probeIdealCoherentTrace_scale_mk (P : HeightOneSpectrum (𝓞 K)) (n k : ℕ) (x : 𝓞 K) :
    probeIdealCoherentTrace K P (n + k)
      (Ideal.Quotient.mk _ (probeIdealUniformizer P ^ k * x)) =
        probeIdealCoherentTrace K P n (Ideal.Quotient.mk _ x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : probeIdealUniformizer P ^ (k + 1) * x =
        probeIdealUniformizer P * (probeIdealUniformizer P ^ k * x) := by
      rw [pow_succ', mul_assoc]
    change probeIdealCoherentTrace K P ((n + k) + 1)
      (Ideal.Quotient.mk _ (probeIdealUniformizer P ^ (k + 1) * x)) = _
    rw [he, probeIdealCoherentTrace_step_mk, ih]

theorem probeIdealCoherentTrace_lower (P : HeightOneSpectrum (𝓞 K)) (n k : ℕ) :
    probePrimePowerLowerChar P n k (probeIdealCoherentTrace K P (n + k)) =
      probeIdealCoherentTrace K P n := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [probePrimePowerLowerChar_mk, probeIdealCoherentTrace_scale_mk]

end

end ArtinMatthews.VaryingKummerAnalytic
