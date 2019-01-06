Require Imp.ImpInterp.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlString.

Extraction Blacklist Nat.
Extraction Blacklist List.
Extraction Blacklist String.

Extract Constant Imp.ImpCommon.extcall => "ImpLib.extcall".

Cd "extract".
Separate Extraction Imp.ImpInterp.interp_p.
Cd "..".
