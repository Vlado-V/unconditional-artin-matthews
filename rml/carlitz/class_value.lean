/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

module

/- Ported to Lean 4.35.0-rc3: removed a now-unused push_cast tactic.
   Original: Charlie Dorsey, Weil Bounds Toolkit, commit
   0f3e4c3010bb0e7c4e514ddb5bd3a0a0e082bf68. Apache-2.0. -/

/- Ported to Lean 4.35.0-rc3: deprecated theorem aliases renamed.
   Original: Charlie Dorsey, Weil Bounds Toolkit, commit
   0f3e4c3010bb0e7c4e514ddb5bd3a0a0e082bf68. Apache-2.0. -/

public import rml.carlitz.dickson_finite_algebra
public import rml.carlitz.extension_defs
public import rml.carlitz.minpoly_inverse

@[expose] public section

/-!
# Trace characters of polynomial classes

Relates extension-field trace characters to values on polynomial classes. The
underlying construction follows Carlitz (1969).
-/

namespace RML.ExpSum.Carlitz

open Polynomial

lemma trace_carlitz_arg
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (t : K) {x : L} (hx : x ≠ 0) :
    Algebra.trace K L
        (x + algebraMap K L t * x⁻¹) =
      (Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L : K) *
        (-(minpoly K x).nextCoeff -
          t * ((minpoly K x).coeff 1 / (minpoly K x).coeff 0)) := by
  have hxtrace :=
    trace_eq_finrank_mul_minpoly_nextCoeff (K := K) x
  have hinvtrace :=
    trace_eq_finrank_mul_minpoly_nextCoeff (K := K) x⁻¹
  have hfin :
      Module.finrank (IntermediateField.adjoin K ({x⁻¹} : Set L)) L =
        Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L := by
    rw [adjoin_inv_eq_adjoin hx]
  have hnext :=
    minpoly_inv_nextCoeff_eq_coeff_one_div_coeff_zero
      (K := K) (L := L) hx
  rw [map_add]
  rw [show algebraMap K L t * x⁻¹ = t • x⁻¹ by
    rw [Algebra.smul_def]]
  rw [map_smul]
  rw [hxtrace, hinvtrace, hfin, hnext]
  ring

#print axioms trace_carlitz_arg


theorem psiExt_carlitz_arg_eq_etaPoly_pow
    (p n : ℕ) [Fact p.Prime] [NeZero n]
    (t : Fp p) {x : Ext p n} (hx : x ≠ 0) :
    psiExt p n
        (x + algebraMap (Fp p) (Ext p n) t * x⁻¹) =
      RML.ExpSum.Dickson.etaPoly p t (minpoly (Fp p) x) ^
        Module.finrank
          (IntermediateField.adjoin (Fp p) ({x} : Set (Ext p n)))
          (Ext p n) := by
  have hc :
      (minpoly (Fp p) x).coeff 0 ≠ 0 :=
    minpoly_coeff_zero_ne_zero_of_ne_zero hx
  rw [show psiExt p n
      (x + algebraMap (Fp p) (Ext p n) t * x⁻¹) =
      ZMod.stdAddChar
        (Algebra.trace (Fp p) (Ext p n)
          (x + algebraMap (Fp p) (Ext p n) t * x⁻¹)) by rfl]
  rw [trace_carlitz_arg t hx]
  unfold RML.ExpSum.Dickson.etaPoly
  rw [dite_eq_right hc]
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul]

#print axioms psiExt_carlitz_arg_eq_etaPoly_pow

end RML.ExpSum.Carlitz
