
(* File automatically generated by Hacspec *)
From Coq Require Import ZArith.
Require Import List.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Require Import Ascii.
Require Import String.
Require Import Coq.Floats.Floats.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* From Core Require Import Core. *)

From Core Require Import Core_Base_interface.
Export Core_Base_interface.

From Core Require Import Core_Primitive.
Export Core_Primitive.

From Core Require Import Core_Intrinsics.
Export Core_Intrinsics.

From Core Require Import Core_Ops_Index.
Export Core_Ops_Index.

(* NotImplementedYet *)

(* NotImplementedYet *)

Notation "'impl_10__from_le'" := (from_le715594649).

Notation "'impl_10__to_le'" := (to_le902648378).

Notation "'impl_7__from_le'" := (from_le793045973).

Notation "'impl_7__to_le'" := (to_le1012469456).

Notation "'impl_8__from_le'" := (from_le706338679).

Notation "'impl_8__to_le'" := (to_le724624277).

Notation "'impl_9__from_le'" := (from_le435089922).

Notation "'impl_9__to_le'" := (to_le2703875).

Notation "'impl_6__from_le'" := (from_le529489651).

Notation "'impl_6__to_le'" := (to_le523556665).

Notation "'impl_11__from_le'" := (from_le418743864).

Notation "'impl_11__to_le'" := (to_le946822077).

Notation "'impl__BITS'" := (v_BITS80497669).

Notation "'impl__MAX'" := (v_MAX626626007).

Notation "'impl__MIN'" := (v_MIN19747349).

Notation "'impl__i16__BITS'" := (v_BITS421056295).

Notation "'impl__i16__MAX'" := (v_MAX474501300).

Notation "'impl__i16__MIN'" := (v_MIN776391606).

Notation "'impl__i32__BITS'" := (v_BITS465526498).

Notation "'impl__i32__MAX'" := (v_MAX106630818).

Notation "'impl__i32__MIN'" := (v_MIN682967538).

Notation "'impl__i64__BITS'" := (v_BITS419886578).

Notation "'impl__i64__MAX'" := (v_MAX527043787).

Notation "'impl__i64__MIN'" := (v_MIN654206259).

Notation "'impl__i128__BITS'" := (v_BITS992667165).

Notation "'impl__i128__MAX'" := (v_MAX375377319).

Notation "'impl__i128__MIN'" := (v_MIN79612531).

Notation "'impl__isize__BITS'" := (v_BITS211584016).

Notation "'impl__isize__MAX'" := (v_MAX937003029).

Notation "'impl__isize__MIN'" := (v_MIN1017039533).

Notation "'impl_6__BITS'" := (v_BITS690311813).

Notation "'impl_6__MAX'" := (v_MAX310118176).

Notation "'impl_6__MIN'" := (v_MIN41851434).

Notation "'impl_7__BITS'" := (v_BITS277333551).

Notation "'impl_7__MAX'" := (v_MAX487295910).

Notation "'impl_7__MIN'" := (v_MIN592300287).

Notation "'impl_8__BITS'" := (v_BITS473478051).

Notation "'impl_8__MAX'" := (v_MAX826434525).

Notation "'impl_8__MIN'" := (v_MIN932777089).

Notation "'impl_9__BITS'" := (v_BITS177666292).

Notation "'impl_9__MAX'" := (v_MAX815180633).

Notation "'impl_9__MIN'" := (v_MIN631333594).

Notation "'impl_10__BITS'" := (v_BITS136999051).

Notation "'impl_10__MAX'" := (v_MAX404543799).

Notation "'impl_10__MIN'" := (v_MIN668621698).

Notation "'impl_11__BITS'" := (v_BITS229952196).

Notation "'impl_11__MAX'" := (v_MAX750570916).

Notation "'impl_11__MIN'" := (v_MIN861571008).

Notation "'impl__is_negative'" := (is_negative350273175).

Notation "'impl__is_positive'" := (is_positive286955196).

Notation "'impl__signum'" := (signum721334203).

Notation "'impl__i16__is_negative'" := (is_negative477067241).

Notation "'impl__i16__is_positive'" := (is_positive821581438).

Notation "'impl__i16__signum'" := (signum243706004).

Notation "'impl__i32__is_negative'" := (is_negative1035644813).

Notation "'impl__i32__is_positive'" := (is_positive401652342).

Notation "'impl__i32__signum'" := (signum323641039).

Notation "'impl__i64__is_negative'" := (is_negative1066124578).

Notation "'impl__i64__is_positive'" := (is_positive16569358).

Notation "'impl__i64__signum'" := (signum582963664).

Notation "'impl__i128__is_negative'" := (is_negative221698470).

Notation "'impl__i128__is_positive'" := (is_positive883218309).

Notation "'impl__i128__signum'" := (signum408800799).

Notation "'impl__isize__is_negative'" := (is_negative693446369).

Notation "'impl__isize__is_positive'" := (is_positive169998680).

Notation "'impl__isize__signum'" := (signum91486536).

Notation "'impl_6__checked_add'" := (checked_add268751055).

Notation "'impl_7__checked_add'" := (checked_add132377399).

Notation "'impl_8__checked_add'" := (checked_add985437730).

Notation "'impl_9__checked_add'" := (checked_add586246465).

Notation "'impl_10__checked_add'" := (checked_add218978451).

Notation "'impl_11__checked_add'" := (checked_add984013567).

Notation "'impl__wrapping_add'" := (wrapping_add634491935).

Notation "'impl__wrapping_sub'" := (wrapping_sub973428293).

Notation "'impl__wrapping_neg'" := (wrapping_neg400701205).

Notation "'impl__wrapping_abs'" := (wrapping_abs400396545).

Notation "'impl__i16__wrapping_add'" := (wrapping_add868559108).

Notation "'impl__i16__wrapping_sub'" := (wrapping_sub189469152).

Notation "'impl__i16__wrapping_neg'" := (wrapping_neg860505723).

Notation "'impl__i16__wrapping_abs'" := (wrapping_abs229076826).

Notation "'impl__i32__wrapping_add'" := (wrapping_add475006616).

Notation "'impl__i32__wrapping_sub'" := (wrapping_sub298337071).

Notation "'impl__i32__wrapping_neg'" := (wrapping_neg636433078).

Notation "'impl__i32__wrapping_abs'" := (wrapping_abs729536875).

Notation "'impl__i64__wrapping_add'" := (wrapping_add590074241).

Notation "'impl__i64__wrapping_sub'" := (wrapping_sub334584751).

Notation "'impl__i64__wrapping_neg'" := (wrapping_neg868282938).

Notation "'impl__i64__wrapping_abs'" := (wrapping_abs285829312).

Notation "'impl__i128__wrapping_add'" := (wrapping_add251385439).

Notation "'impl__i128__wrapping_sub'" := (wrapping_sub681598071).

Notation "'impl__i128__wrapping_neg'" := (wrapping_neg446546984).

Notation "'impl__i128__wrapping_abs'" := (wrapping_abs281925696).

Notation "'impl__isize__wrapping_add'" := (wrapping_add226040243).

Notation "'impl__isize__wrapping_sub'" := (wrapping_sub698035192).

Notation "'impl__isize__wrapping_neg'" := (wrapping_neg912291768).

Notation "'impl__isize__wrapping_abs'" := (wrapping_abs347300819).

Notation "'impl_6__checked_div'" := (checked_div508301931).

Notation "'impl_6__overflowing_add'" := (overflowing_add708890057).

Notation "'impl_7__checked_div'" := (checked_div614920780).

Notation "'impl_7__overflowing_add'" := (overflowing_add1023344178).

Notation "'impl_8__checked_div'" := (checked_div979383477).

Notation "'impl_8__overflowing_add'" := (overflowing_add905744292).

Notation "'impl_9__checked_div'" := (checked_div988689127).

Notation "'impl_9__overflowing_add'" := (overflowing_add581983607).

Notation "'impl_10__checked_div'" := (checked_div344106746).

Notation "'impl_10__overflowing_add'" := (overflowing_add458293681).

Notation "'impl_11__checked_div'" := (checked_div80223906).

Notation "'impl_11__overflowing_add'" := (overflowing_add682280407).

Notation "'impl__abs'" := (abs945505614).

Notation "'impl__i16__abs'" := (abs581170970).

Notation "'impl__i32__abs'" := (abs590464694).

Notation "'impl__i64__abs'" := (abs654781043).

Notation "'impl__i128__abs'" := (abs204417539).

Notation "'impl__isize__abs'" := (abs220926056).

Notation "'impl_6__wrapping_add'" := (wrapping_add480603777).

Notation "'impl_6__wrapping_mul'" := (wrapping_mul885216284).

Notation "'impl_7__wrapping_add'" := (wrapping_add124432709).

Notation "'impl_7__wrapping_mul'" := (wrapping_mul14465189).

Notation "'impl_8__wrapping_add'" := (wrapping_add1049665857).

Notation "'impl_8__wrapping_mul'" := (wrapping_mul203346768).

Notation "'impl_9__wrapping_add'" := (wrapping_add865565639).

Notation "'impl_9__wrapping_mul'" := (wrapping_mul742978873).

Notation "'impl_10__wrapping_add'" := (wrapping_add40844100).

Notation "'impl_10__wrapping_mul'" := (wrapping_mul294115024).

Notation "'impl_11__wrapping_add'" := (wrapping_add427637036).

Notation "'impl_11__wrapping_mul'" := (wrapping_mul680896953).

Notation "'impl_6__wrapping_sub'" := (wrapping_sub403906422).

Notation "'impl_6__wrapping_neg'" := (wrapping_neg123212788).

Notation "'impl_7__wrapping_sub'" := (wrapping_sub811251034).

Notation "'impl_7__wrapping_neg'" := (wrapping_neg128555595).

Notation "'impl_8__wrapping_sub'" := (wrapping_sub708953500).

Notation "'impl_8__wrapping_neg'" := (wrapping_neg328220773).

Notation "'impl_9__wrapping_sub'" := (wrapping_sub762520851).

Notation "'impl_9__wrapping_neg'" := (wrapping_neg617136337).

Notation "'impl_10__wrapping_sub'" := (wrapping_sub409310259).

Notation "'impl_10__wrapping_neg'" := (wrapping_neg729451428).

Notation "'impl_11__wrapping_sub'" := (wrapping_sub813101882).

Notation "'impl_11__wrapping_neg'" := (wrapping_neg342773446).

Notation "'impl_6__wrapping_div'" := (wrapping_div660080892).

Notation "'impl_6__wrapping_div_euclid'" := (wrapping_div_euclid481233436).

Notation "'impl_7__wrapping_div'" := (wrapping_div366977334).

Notation "'impl_7__wrapping_div_euclid'" := (wrapping_div_euclid22267888).

Notation "'impl_8__wrapping_div'" := (wrapping_div931150450).

Notation "'impl_8__wrapping_div_euclid'" := (wrapping_div_euclid606291997).

Notation "'impl_9__wrapping_div'" := (wrapping_div168427046).

Notation "'impl_9__wrapping_div_euclid'" := (wrapping_div_euclid321252086).

Notation "'impl_10__wrapping_div'" := (wrapping_div692427683).

Notation "'impl_10__wrapping_div_euclid'" := (wrapping_div_euclid926334515).

Notation "'impl_11__wrapping_div'" := (wrapping_div905768546).

Notation "'impl_11__wrapping_div_euclid'" := (wrapping_div_euclid90317722).

Notation "'impl_6__wrapping_rem'" := (wrapping_rem984569721).

Notation "'impl_6__wrapping_rem_euclid'" := (wrapping_rem_euclid946579345).

Notation "'impl_7__wrapping_rem'" := (wrapping_rem378598035).

Notation "'impl_7__wrapping_rem_euclid'" := (wrapping_rem_euclid602402638).

Notation "'impl_8__wrapping_rem'" := (wrapping_rem292009099).

Notation "'impl_8__wrapping_rem_euclid'" := (wrapping_rem_euclid1020271291).

Notation "'impl_9__wrapping_rem'" := (wrapping_rem390602260).

Notation "'impl_9__wrapping_rem_euclid'" := (wrapping_rem_euclid839264546).

Notation "'impl_10__wrapping_rem'" := (wrapping_rem332379920).

Notation "'impl_10__wrapping_rem_euclid'" := (wrapping_rem_euclid646122423).

Notation "'impl_11__wrapping_rem'" := (wrapping_rem333089373).

Notation "'impl_11__wrapping_rem_euclid'" := (wrapping_rem_euclid769656504).

Notation "'impl_6__rotate_left'" := (rotate_left792925914).

Notation "'impl_6__rotate_right'" := (rotate_right166090082).

Notation "'impl_7__rotate_left'" := (rotate_left297034175).

Notation "'impl_7__rotate_right'" := (rotate_right138522246).

Notation "'impl_8__rotate_left'" := (rotate_left823573251).

Notation "'impl_8__rotate_right'" := (rotate_right869195717).

Notation "'impl_9__rotate_left'" := (rotate_left618936072).

Notation "'impl_9__rotate_right'" := (rotate_right1041614027).

Notation "'impl_10__rotate_left'" := (rotate_left1065866885).

Notation "'impl_10__rotate_right'" := (rotate_right591112338).

Notation "'impl_11__rotate_left'" := (rotate_left996672710).

Notation "'impl_11__rotate_right'" := (rotate_right442734174).

(* Notation "'impl_6__count_ones'" := (count_ones202509899). *)

(* Notation "'impl_6__leading_zeros'" := (leading_zeros75047366). *)

(* Notation "'impl_6__swap_bytes'" := (swap_bytes657156997). *)

(* Notation "'impl_6__from_be'" := (from_be746282521). *)

(* Notation "'impl_6__to_be'" := (to_be972448780). *)

(* Notation "'impl_6__trailing_zeros'" := (trailing_zeros572929871). *)

(* Notation "'impl_7__count_ones'" := (count_ones91875752). *)

(* Notation "'impl_7__leading_zeros'" := (leading_zeros462412478). *)

(* Notation "'impl_7__swap_bytes'" := (swap_bytes926722059). *)

(* Notation "'impl_7__from_be'" := (from_be510959665). *)

(* Notation "'impl_7__to_be'" := (to_be551590602). *)

(* Notation "'impl_7__trailing_zeros'" := (trailing_zeros421474733). *)

(* Notation "'impl_8__count_ones'" := (count_ones776185738). *)

(* Notation "'impl_8__leading_zeros'" := (leading_zeros698221972). *)

(* Notation "'impl_8__swap_bytes'" := (swap_bytes320480126). *)

(* Notation "'impl_8__from_be'" := (from_be664756649). *)

(* Notation "'impl_8__to_be'" := (to_be82825962). *)

(* Notation "'impl_8__trailing_zeros'" := (trailing_zeros1061560720). *)

(* Notation "'impl_9__count_ones'" := (count_ones235885653). *)

(* Notation "'impl_9__leading_zeros'" := (leading_zeros338302110). *)

(* Notation "'impl_9__swap_bytes'" := (swap_bytes722254271). *)

(* Notation "'impl_9__from_be'" := (from_be16013635). *)

(* Notation "'impl_9__to_be'" := (to_be376714729). *)

(* Notation "'impl_9__trailing_zeros'" := (trailing_zeros188346231). *)

(* Notation "'impl_10__count_ones'" := (count_ones926736261). *)

(* Notation "'impl_10__leading_zeros'" := (leading_zeros19644612). *)

(* Notation "'impl_10__swap_bytes'" := (swap_bytes420879368). *)

(* Notation "'impl_10__from_be'" := (from_be191085771). *)

(* Notation "'impl_10__to_be'" := (to_be555075987). *)

(* Notation "'impl_10__trailing_zeros'" := (trailing_zeros821715250). *)

(* Notation "'impl_11__count_ones'" := (count_ones441645762). *)

(* Notation "'impl_11__leading_zeros'" := (leading_zeros905233489). *)

(* Notation "'impl_11__swap_bytes'" := (swap_bytes268673424). *)

(* Notation "'impl_11__from_be'" := (from_be607978059). *)

(* Notation "'impl_11__to_be'" := (to_be561847134). *)

(* Notation "'impl_11__trailing_zeros'" := (trailing_zeros42066260). *)

Notation "'impl__rem_euclid'" := (rem_euclid622298453).

Notation "'impl__i16__rem_euclid'" := (rem_euclid158017644).

Notation "'impl__i32__rem_euclid'" := (rem_euclid881249982).

Notation "'impl__i64__rem_euclid'" := (rem_euclid1057082210).

Notation "'impl__i128__rem_euclid'" := (rem_euclid254910751).

Notation "'impl__isize__rem_euclid'" := (rem_euclid828379367).

(* Notation "'impl_6__count_zeros'" := (count_zeros558337492). *)

(* Notation "'impl_6__leading_ones'" := (leading_ones55148479). *)

(* Notation "'impl_6__trailing_ones'" := (trailing_ones359778731). *)

(* Notation "'impl_7__count_zeros'" := (count_zeros199825317). *)

(* Notation "'impl_7__leading_ones'" := (leading_ones164277656). *)

(* Notation "'impl_7__trailing_ones'" := (trailing_ones903944727). *)

(* Notation "'impl_8__count_zeros'" := (count_zeros942566041). *)

(* Notation "'impl_8__leading_ones'" := (leading_ones766486760). *)

(* Notation "'impl_8__trailing_ones'" := (trailing_ones223371510). *)

(* Notation "'impl_9__count_zeros'" := (count_zeros60346158). *)

(* Notation "'impl_9__leading_ones'" := (leading_ones404666910). *)

(* Notation "'impl_9__trailing_ones'" := (trailing_ones601201120). *)

(* Notation "'impl_10__count_zeros'" := (count_zeros824862815). *)

(* Notation "'impl_10__leading_ones'" := (leading_ones475503572). *)

(* Notation "'impl_10__trailing_ones'" := (trailing_ones705845381). *)

(* Notation "'impl_11__count_zeros'" := (count_zeros73479642). *)

(* Notation "'impl_11__leading_ones'" := (leading_ones667660708). *)

(* Notation "'impl_11__trailing_ones'" := (trailing_ones979548463). *)