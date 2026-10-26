import NLA.Proofs.TR04.MachineTTForward
import NLA.Proofs.TR04.MachineTTInitializationTrace

/-! Literal reverse metadata read preparations and lifting continuation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
private theorem ttReverse_naturals : ttProgram.extraNatRegisters=127 := rfl
private theorem ttReverse_reals : ttProgram.realRegisters=16 := rfl
theorem ttProgram_code_reverse_286 : ttProgram.code 286 = .decrement (⟨84,by decide⟩ : Fin 128) (⟨287,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_287 : ttProgram.code 287 = .mulNat (⟨93,by decide⟩ : Fin 128) (⟨125,by decide⟩ : Fin 128) (⟨84,by decide⟩ : Fin 128) (⟨288,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_288 : ttProgram.code 288 = .addNat (⟨93,by decide⟩ : Fin 128) (⟨68,by decide⟩ : Fin 128) (⟨93,by decide⟩ : Fin 128) (⟨289,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_289 : ttProgram.code 289 = .read (⟨0,by decide⟩ : Fin 16) (⟨93,by decide⟩ : Fin 128) (⟨290,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_290 : ttProgram.code 290 = .copyNat (⟨1,by decide⟩ : Fin 128) (⟨0,by decide⟩ : Fin 128) (⟨291,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_291 : ttProgram.code 291 = .natural (⟨2,by decide⟩ : Fin 128) 1 (⟨292,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_292 : ttProgram.code 292 = .natural (⟨3,by decide⟩ : Fin 128) 0 (⟨293,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_293 : ttProgram.code 293 = .natural (⟨97,by decide⟩ : Fin 128) 7 (⟨294,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_294 : ttProgram.code 294 = .jump (⟨5,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_295 : ttProgram.code 295 = .copyNat (⟨85,by decide⟩ : Fin 128) (⟨2,by decide⟩ : Fin 128) (⟨296,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_296 : ttProgram.code 296 = .increment (⟨93,by decide⟩ : Fin 128) (⟨297,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_297 : ttProgram.code 297 = .read (⟨0,by decide⟩ : Fin 16) (⟨93,by decide⟩ : Fin 128) (⟨298,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_298 : ttProgram.code 298 = .copyNat (⟨1,by decide⟩ : Fin 128) (⟨0,by decide⟩ : Fin 128) (⟨299,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_299 : ttProgram.code 299 = .natural (⟨2,by decide⟩ : Fin 128) 1 (⟨300,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_300 : ttProgram.code 300 = .natural (⟨3,by decide⟩ : Fin 128) 0 (⟨301,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_301 : ttProgram.code 301 = .natural (⟨97,by decide⟩ : Fin 128) 8 (⟨302,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_302 : ttProgram.code 302 = .jump (⟨5,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_303 : ttProgram.code 303 = .copyNat (⟨86,by decide⟩ : Fin 128) (⟨2,by decide⟩ : Fin 128) (⟨304,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_304 : ttProgram.code 304 = .increment (⟨93,by decide⟩ : Fin 128) (⟨305,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_305 : ttProgram.code 305 = .read (⟨0,by decide⟩ : Fin 16) (⟨93,by decide⟩ : Fin 128) (⟨306,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_306 : ttProgram.code 306 = .copyNat (⟨1,by decide⟩ : Fin 128) (⟨0,by decide⟩ : Fin 128) (⟨307,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_307 : ttProgram.code 307 = .natural (⟨2,by decide⟩ : Fin 128) 1 (⟨308,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_308 : ttProgram.code 308 = .natural (⟨3,by decide⟩ : Fin 128) 0 (⟨309,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_309 : ttProgram.code 309 = .natural (⟨97,by decide⟩ : Fin 128) 9 (⟨310,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_310 : ttProgram.code 310 = .jump (⟨5,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_311 : ttProgram.code 311 = .copyNat (⟨87,by decide⟩ : Fin 128) (⟨2,by decide⟩ : Fin 128) (⟨312,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_312 : ttProgram.code 312 = .increment (⟨93,by decide⟩ : Fin 128) (⟨313,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_313 : ttProgram.code 313 = .read (⟨0,by decide⟩ : Fin 16) (⟨93,by decide⟩ : Fin 128) (⟨314,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_314 : ttProgram.code 314 = .copyNat (⟨1,by decide⟩ : Fin 128) (⟨0,by decide⟩ : Fin 128) (⟨315,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_315 : ttProgram.code 315 = .natural (⟨2,by decide⟩ : Fin 128) 1 (⟨316,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_316 : ttProgram.code 316 = .natural (⟨3,by decide⟩ : Fin 128) 0 (⟨317,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_317 : ttProgram.code 317 = .natural (⟨97,by decide⟩ : Fin 128) 10 (⟨318,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_318 : ttProgram.code 318 = .jump (⟨5,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_319 : ttProgram.code 319 = .copyNat (⟨88,by decide⟩ : Fin 128) (⟨2,by decide⟩ : Fin 128) (⟨320,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_320 : ttProgram.code 320 = .mulNat (⟨94,by decide⟩ : Fin 128) (⟨84,by decide⟩ : Fin 128) (⟨66,by decide⟩ : Fin 128) (⟨321,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_321 : ttProgram.code 321 = .addNat (⟨94,by decide⟩ : Fin 128) (⟨67,by decide⟩ : Fin 128) (⟨94,by decide⟩ : Fin 128) (⟨322,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_322 : ttProgram.code 322 = .copyNat (⟨4,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨323,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_323 : ttProgram.code 323 = .copyNat (⟨5,by decide⟩ : Fin 128) (⟨87,by decide⟩ : Fin 128) (⟨324,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_324 : ttProgram.code 324 = .copyNat (⟨6,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨325,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_325 : ttProgram.code 325 = .copyNat (⟨7,by decide⟩ : Fin 128) (⟨85,by decide⟩ : Fin 128) (⟨326,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_326 : ttProgram.code 326 = .copyNat (⟨8,by decide⟩ : Fin 128) (⟨86,by decide⟩ : Fin 128) (⟨327,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_327 : ttProgram.code 327 = .copyNat (⟨9,by decide⟩ : Fin 128) (⟨87,by decide⟩ : Fin 128) (⟨328,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_328 : ttProgram.code 328 = .copyNat (⟨10,by decide⟩ : Fin 128) (⟨94,by decide⟩ : Fin 128) (⟨329,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_329 : ttProgram.code 329 = .copyNat (⟨11,by decide⟩ : Fin 128) (⟨89,by decide⟩ : Fin 128) (⟨330,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_330 : ttProgram.code 330 = .copyNat (⟨12,by decide⟩ : Fin 128) (⟨90,by decide⟩ : Fin 128) (⟨331,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_331 : ttProgram.code 331 = .copyNat (⟨13,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨332,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_332 : ttProgram.code 332 = .copyNat (⟨14,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨333,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_333 : ttProgram.code 333 = .copyNat (⟨15,by decide⟩ : Fin 128) (⟨90,by decide⟩ : Fin 128) (⟨334,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_334 : ttProgram.code 334 = .copyNat (⟨16,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨335,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_335 : ttProgram.code 335 = .copyNat (⟨17,by decide⟩ : Fin 128) (⟨88,by decide⟩ : Fin 128) (⟨336,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_336 : ttProgram.code 336 = .copyNat (⟨18,by decide⟩ : Fin 128) (⟨126,by decide⟩ : Fin 128) (⟨337,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_337 : ttProgram.code 337 = .copyNat (⟨19,by decide⟩ : Fin 128) (⟨87,by decide⟩ : Fin 128) (⟨338,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_338 : ttProgram.code 338 = .copyNat (⟨20,by decide⟩ : Fin 128) (⟨126,by decide⟩ : Fin 128) (⟨339,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_339 : ttProgram.code 339 = .natural (⟨97,by decide⟩ : Fin 128) 2 (⟨340,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_340 : ttProgram.code 340 = .jump (⟨11,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_341 : ttProgram.code 341 = .copyNat (⟨123,by decide⟩ : Fin 128) (⟨89,by decide⟩ : Fin 128) (⟨342,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_342 : ttProgram.code 342 = .copyNat (⟨89,by decide⟩ : Fin 128) (⟨90,by decide⟩ : Fin 128) (⟨343,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_343 : ttProgram.code 343 = .copyNat (⟨90,by decide⟩ : Fin 128) (⟨123,by decide⟩ : Fin 128) (⟨344,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_344 : ttProgram.code 344 = .equalNat (⟨84,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨347,by decide⟩ : Fin 512) (⟨345,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_345 : ttProgram.code 345 = .decrement (⟨84,by decide⟩ : Fin 128) (⟨346,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_346 : ttProgram.code 346 = .jump (⟨287,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_347 : ttProgram.code 347 = .mulNat (⟨123,by decide⟩ : Fin 128) (⟨76,by decide⟩ : Fin 128) (⟨64,by decide⟩ : Fin 128) (⟨348,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_reverse_348 : ttProgram.code 348 = .addNat (⟨123,by decide⟩ : Fin 128) (⟨71,by decide⟩ : Fin 128) (⟨123,by decide⟩ : Fin 128) (⟨349,by decide⟩ : Fin 512) := rfl

def ttReverseReadLabel (k : Fin 4) : Fin 512 :=
  if k.val=0 then 287 else ⟨287+8*k.val,by have := k.isLt;omega⟩

def ttReverseReadHandler (k : Fin 4) : Fin 512 := ⟨295+8*k.val,by have := k.isLt;omega⟩

def ttReverseReadAddress (s : State ttProgram) (k : Fin 4) : ℕ :=
  if k.val=0 then s.natural 68+4*s.natural 84 else s.natural 93+1

def ttReverseReadNatural (s : State ttProgram) (k : Fin 4) : Fin 128 → ℕ :=
  let old := if k.val=0 then s.natural else
    Function.update s.natural (⟨84+k.val,by have := k.isLt;omega⟩ : Fin 128) (s.natural 2)
  Function.update (Function.update (Function.update (Function.update
    (Function.update old 93 (ttReverseReadAddress s k)) 1 (s.natural 0)) 2 1) 3 0) 97 (7+k.val)

def ttReverseReadEntry (s : State ttProgram) (k : Fin 4) : State ttProgram where
  label := 5
  real := Function.update s.real (0 : Fin 16) (s.memory (ttReverseReadAddress s k))
  natural := ttReverseReadNatural s k
  memory := s.memory
  status := .running

 theorem ttReverseRead_steps (s : State ttProgram) (k : Fin 4)
    (hl : s.label=ttReverseReadLabel k) (hs : s.status=.running) (hfour : s.natural 125=4) :
    (ordinaryStep ttProgram)^[8] s=ttReverseReadEntry s k := by
  fin_cases k
  all_goals apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.iterate_succ_apply',ordinaryStep,hl,hs,hfour,
    ttReverse_naturals,ttReverse_reals,ttReverseReadLabel,ttReverseReadAddress,
    ttReverseReadNatural,ttReverseReadEntry,
    ttProgram_code_reverse_287,ttProgram_code_reverse_288,ttProgram_code_reverse_289,ttProgram_code_reverse_290,ttProgram_code_reverse_291,ttProgram_code_reverse_292,ttProgram_code_reverse_293,ttProgram_code_reverse_294,ttProgram_code_reverse_295,ttProgram_code_reverse_296,ttProgram_code_reverse_297,ttProgram_code_reverse_298,ttProgram_code_reverse_299,ttProgram_code_reverse_300,ttProgram_code_reverse_301,ttProgram_code_reverse_302,ttProgram_code_reverse_303,ttProgram_code_reverse_304,ttProgram_code_reverse_305,ttProgram_code_reverse_306,ttProgram_code_reverse_307,ttProgram_code_reverse_308,ttProgram_code_reverse_309,ttProgram_code_reverse_310,ttProgram_code_reverse_311,ttProgram_code_reverse_312,ttProgram_code_reverse_313,ttProgram_code_reverse_314,ttProgram_code_reverse_315,ttProgram_code_reverse_316,ttProgram_code_reverse_317,ttProgram_code_reverse_318]

#assert_trust kernel ttReverseRead_steps
#print axioms ttReverseRead_steps
end NLA.Proofs.TR04
