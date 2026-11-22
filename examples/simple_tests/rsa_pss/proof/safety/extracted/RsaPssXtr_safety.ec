require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import
Array3 Array4 Array16 Array24 Array32 Array36 Array64 Array65 Array80
Array128 Array129 Array133 Array178 Array256 Array288 Array512 Array520
Array640 Array1032 Array1064 Array1424 Array2048 WArray288 WArray640 BArray24
BArray32 BArray128 BArray256 BArray288 BArray512 BArray520 BArray640
BArray1032 BArray1064 BArray1424 BArray2048 SBArray1064_32 SBArray256_128
SBArray520_128 SBArray640_128 SBArray1424_128 SBArray2048_128 SBArray288_256
SBArray512_256 SBArray520_256 SBArray1032_256 SBArray1032_512 SBArray1424_520
SBArray1064_1032.

abbrev  sk_test =
(BArray640.of_list64
[(W64.of_int (-5814336165028313825)); (W64.of_int (-3164325282885671618));
(W64.of_int (-4875755643669347319)); (W64.of_int (-8123408433426048574));
(W64.of_int 4717983966628017497); (W64.of_int (-4578546088516889899));
(W64.of_int 2542687746355288030); (W64.of_int (-8943137896182142999));
(W64.of_int (-7743862190675052995)); (W64.of_int (-5016358049760372204));
(W64.of_int (-2618720524856169351)); (W64.of_int (-6370930581725028336));
(W64.of_int 3451203149785967789); (W64.of_int 711204276789105955);
(W64.of_int (-30367224164026964)); (W64.of_int (-1320225356120947196));
(W64.of_int (-2546923399851779729)); (W64.of_int 3157134082718893467);
(W64.of_int (-3930188011914496701)); (W64.of_int (-6338036845434304740));
(W64.of_int 6501634704600495392); (W64.of_int (-7254385447830332240));
(W64.of_int 5956947459813090175); (W64.of_int 8976661214561183395);
(W64.of_int (-1268587582221850801)); (W64.of_int 5863889395760015806);
(W64.of_int (-8563668383581105322)); (W64.of_int 1746792491480712789);
(W64.of_int 4534681187726714117); (W64.of_int 4147124906443555845);
(W64.of_int (-3682022165819156421)); (W64.of_int (-389179986429542652));
(W64.of_int (-4881427620503570697)); (W64.of_int 4437599631610253315);
(W64.of_int 5434726464013597451); (W64.of_int (-1840817614603703335));
(W64.of_int 2031149012413792506); (W64.of_int 5889046994089609850);
(W64.of_int 6581489053236809176); (W64.of_int (-8779658519650116706));
(W64.of_int (-7434957583256165835)); (W64.of_int 7575134967904308220);
(W64.of_int 7402883375718405742); (W64.of_int 3078149144570467343);
(W64.of_int (-6192524814449428089)); (W64.of_int 7683646776073297976);
(W64.of_int (-6379045659589979679)); (W64.of_int 4169978167700098581);
(W64.of_int (-4535429363158792985)); (W64.of_int 5067558506218235293);
(W64.of_int 3263793342042990384); (W64.of_int (-6570691044900464764));
(W64.of_int (-5737460086676373745)); (W64.of_int 7695966145636381837);
(W64.of_int 603589614302621658); (W64.of_int (-2200897770459536549));
(W64.of_int (-5904826666613837665)); (W64.of_int (-8158211561235867095));
(W64.of_int (-4045644499183505943)); (W64.of_int (-6254843048144517391));
(W64.of_int (-710787402770479723)); (W64.of_int (-4021697095853109538));
(W64.of_int 4356016818928901334); (W64.of_int (-5740018361316671664));
(W64.of_int (-92106211052834656)); (W64.of_int 8242853796551249280);
(W64.of_int (-7348370292295554880)); (W64.of_int 1485678028952478250);
(W64.of_int (-2533278944601182182)); (W64.of_int 5195411757922833764);
(W64.of_int 8875421771578390968); (W64.of_int (-2395777855256387010));
(W64.of_int (-4794326779914374192)); (W64.of_int (-328448065630490828));
(W64.of_int (-4581303681702531991)); (W64.of_int 4060221158069661258);
(W64.of_int (-3099851117687429757)); (W64.of_int 5004928967557116700);
(W64.of_int 3964966756513499960); (W64.of_int 9112084412970702696)]).

abbrev  pk_test =
(BArray288.of_list64
[(W64.of_int (-3766931495106494607)); (W64.of_int (-5234840375675812656));
(W64.of_int (-7831787053721401243)); (W64.of_int 8997906205628982439);
(W64.of_int (-5365631430910343871)); (W64.of_int (-2425790193533139652));
(W64.of_int 4805521551574280292); (W64.of_int (-7469124577199937167));
(W64.of_int 5739933100300233785); (W64.of_int (-5576291125429710883));
(W64.of_int (-4941681143056970042)); (W64.of_int (-475202404758310692));
(W64.of_int (-8574546828751248825)); (W64.of_int 7511966324222895169);
(W64.of_int (-3770870834343919743)); (W64.of_int (-4536405402184069284));
(W64.of_int 6806829317882269337); (W64.of_int 9148033715187843692);
(W64.of_int (-4640214297950309761)); (W64.of_int (-586045975045317813));
(W64.of_int (-6432880458656861036)); (W64.of_int (-3574336660635036045));
(W64.of_int 3331466668151873461); (W64.of_int (-4872405787113686432));
(W64.of_int 984839058634319491); (W64.of_int (-7115266000952212141));
(W64.of_int (-6583130380393734047)); (W64.of_int 4308353787261133906);
(W64.of_int 5440724217475940828); (W64.of_int (-3020851223251147493));
(W64.of_int 3158400495748471517); (W64.of_int (-1681551902174994651));
(W64.of_int 65537); (W64.of_int 0); (W64.of_int 0); (W64.of_int 0)]).

module M = {
  var tmp__trace : trace
  proc uTIL____mask_cf (mask:W64.t) : bool * trace = {
    var t:W64.t;
    var cf:bool;
    var trace_uTIL____mask_cf:trace;
    trace_uTIL____mask_cf <- [];
    t <- (W64.of_int 0);
    (cf, t) <- (sbb_64 t mask false);
    return (cf, trace_uTIL____mask_cf);
  }
  proc uTIL____cf_mask (cf:bool) : W64.t * trace = {
    var mask:W64.t;
    var  _0:bool;
    var trace_uTIL____cf_mask:trace;
    trace_uTIL____cf_mask <- [];
    mask <- (W64.of_int 0);
    ( _0, mask) <- (sbb_64 mask (W64.of_int 0) cf);
    return (mask, trace_uTIL____cf_mask);
  }
  proc uTIL____addacc3 (a:BArray24.t, b_a:BArray24.t, b1:W64.t, b0:W64.t,
                        k:int) : BArray24.t * BArray24.t * trace = {
    var aux_0:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux:bool;
    var aux_1:bool;
    var aux_3:bool;
    var cf:bool;
    var trace_uTIL____addacc3:trace;
    trace_uTIL____addacc3 <- [];
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++ [(Assert, (BArray24.is_init b_a 0 24))]);
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++
    [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++
    [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
    (aux, aux_0) <- (adc_64 (BArray24.get64 a (k %% 3)) b0 false);
    cf <- aux;
    a <- (BArray24.set64 a (k %% 3) aux_0);
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++
    [(Assert,
     ((0 <= (((k + 1) %% 3) * 8)) /\ (((((k + 1) %% 3) * 8) + 8) <= 24)))]);
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++
    [(Assert,
     ((0 <= (((k + 1) %% 3) * 8)) /\ (((((k + 1) %% 3) * 8) + 8) <= 24)))]);
    (aux_1, aux_2) <- (adc_64 (BArray24.get64 a ((k + 1) %% 3)) b1 cf);
    cf <- aux_1;
    a <- (BArray24.set64 a ((k + 1) %% 3) aux_2);
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++
    [(Assert,
     ((0 <= (((k + 2) %% 3) * 8)) /\ (((((k + 2) %% 3) * 8) + 8) <= 24)))]);
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++
    [(Assert,
     ((0 <= (((k + 2) %% 3) * 8)) /\ (((((k + 2) %% 3) * 8) + 8) <= 24)))]);
    (aux_3, aux_4) <-
    (adc_64 (BArray24.get64 a ((k + 2) %% 3)) (W64.of_int 0) cf);
    cf <- aux_3;
    a <- (BArray24.set64 a ((k + 2) %% 3) aux_4);
    b_a <- (BArray24.init_arr (W8.of_int 255));
    return (a, b_a, trace_uTIL____addacc3);
  }
  proc uTIL____addacc3x2 (a:BArray24.t, b_a:BArray24.t, x:W64.t, y:W64.t,
                          k:int) : BArray24.t * BArray24.t * trace = {
    var aux_0:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux:bool;
    var aux_1:bool;
    var aux_3:bool;
    var b1:W64.t;
    var b0:W64.t;
    var t:W64.t;
    var cf:bool;
    var b2:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_uTIL____addacc3x2:trace;
    trace_uTIL____addacc3x2 <- [];
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++ [(Assert, (BArray24.is_init b_a 0 24))]);
    (b1, b0) <- (mulu_64 x y);
    t <- b0;
    b0 <- (b0 `<<` (W8.of_int 1));
    ( _0, cf,  _1,  _2,  _3, b1) <- (SHLD_64 b1 t (W8.of_int 1));
    b2 <- (MOV_64 (W64.of_int 0));
    (cf, b2) <- (adc_64 b2 b2 cf);
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++
    [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++
    [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
    (aux, aux_0) <- (adc_64 (BArray24.get64 a (k %% 3)) b0 false);
    cf <- aux;
    a <- (BArray24.set64 a (k %% 3) aux_0);
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++
    [(Assert,
     ((0 <= (((k + 1) %% 3) * 8)) /\ (((((k + 1) %% 3) * 8) + 8) <= 24)))]);
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++
    [(Assert,
     ((0 <= (((k + 1) %% 3) * 8)) /\ (((((k + 1) %% 3) * 8) + 8) <= 24)))]);
    (aux_1, aux_2) <- (adc_64 (BArray24.get64 a ((k + 1) %% 3)) b1 cf);
    cf <- aux_1;
    a <- (BArray24.set64 a ((k + 1) %% 3) aux_2);
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++
    [(Assert,
     ((0 <= (((k + 2) %% 3) * 8)) /\ (((((k + 2) %% 3) * 8) + 8) <= 24)))]);
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++
    [(Assert,
     ((0 <= (((k + 2) %% 3) * 8)) /\ (((((k + 2) %% 3) * 8) + 8) <= 24)))]);
    (aux_3, aux_4) <- (adc_64 (BArray24.get64 a ((k + 2) %% 3)) b2 cf);
    cf <- aux_3;
    a <- (BArray24.set64 a ((k + 2) %% 3) aux_4);
    b_a <- (BArray24.init_arr (W8.of_int 255));
    return (a, b_a, trace_uTIL____addacc3x2);
  }
  proc h__H__BN____mov (r:BArray128.t, b_r:BArray128.t, a:BArray128.t,
                        b_a:BArray128.t) : BArray128.t * BArray128.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__H__BN____mov:trace;
    trace_h__H__BN____mov <- [];
    trace_h__H__BN____mov <-
    (trace_h__H__BN____mov ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    i <- 0;
    while ((i < 16)) {
      trace_h__H__BN____mov <-
      (trace_h__H__BN____mov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      t <- (BArray128.get64 a i);
      trace_h__H__BN____mov <-
      (trace_h__H__BN____mov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      b_r <-
      (BArray128.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray128.set64 r i t);
      i <- (i + 1);
    }
    return (r, b_r, trace_h__H__BN____mov);
  }
  proc h__H__BN___mov (r:BArray128.t, b_r:BArray128.t, a:BArray128.t,
                       b_a:BArray128.t) : BArray128.t * BArray128.t * trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___mov:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__H__BN___mov <- [];
    trace_h__H__BN___mov <-
    (trace_h__H__BN___mov ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__H__BN____mov (param, b_param, param_0,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__BN___mov <- (trace_h__H__BN___mov ++ tmp__trace);
    trace_h__H__BN___mov <-
    (trace_h__H__BN___mov ++ [(Assert, (BArray128.is_init b_result 0 128))]);
    r <- result;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__BN___mov);
  }
  proc h__H__BN___mov_ (r:BArray128.t, b_r:BArray128.t, a:BArray128.t,
                        b_a:BArray128.t) : BArray128.t * BArray128.t * trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___mov_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__H__BN___mov_ <- [];
    trace_h__H__BN___mov_ <-
    (trace_h__H__BN___mov_ ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__H__BN___mov (param, b_param, param_0,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__BN___mov_ <- (trace_h__H__BN___mov_ ++ tmp__trace);
    trace_h__H__BN___mov_ <-
    (trace_h__H__BN___mov_ ++ [(Assert, (BArray128.is_init b_result 0 128))]);
    r <- result;
    r <- r;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__BN___mov_);
  }
  proc h__H__BN____cmov (a:BArray128.t, b_a:BArray128.t, cond:bool,
                         b:BArray128.t, b_b:BArray128.t) : BArray128.t *
                                                           BArray128.t *
                                                           trace = {
    var i:int;
    var t:W64.t;
    var trace_h__H__BN____cmov:trace;
    trace_h__H__BN____cmov <- [];
    trace_h__H__BN____cmov <-
    (trace_h__H__BN____cmov ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__BN____cmov <-
    (trace_h__H__BN____cmov ++ [(Assert, (BArray128.is_init b_b 0 128))]);
    i <- 0;
    while ((i < 16)) {
      trace_h__H__BN____cmov <-
      (trace_h__H__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      t <- (BArray128.get64 a i);
      trace_h__H__BN____cmov <-
      (trace_h__H__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      t <- (cond ? (BArray128.get64 b i) : t);
      trace_h__H__BN____cmov <-
      (trace_h__H__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      a <- (BArray128.set64 a i t);
      i <- (i + 1);
    }
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__BN____cmov);
  }
  proc h__H__BN___cmov (a:BArray128.t, b_a:BArray128.t, cond:bool,
                        b:BArray128.t, b_b:BArray128.t) : BArray128.t *
                                                          BArray128.t * trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var param:BArray128.t;
    var param_0:bool;
    var param_1:BArray128.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___cmov:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__BN___cmov <- [];
    trace_h__H__BN___cmov <-
    (trace_h__H__BN___cmov ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__BN___cmov <-
    (trace_h__H__BN___cmov ++ [(Assert, (BArray128.is_init b_b 0 128))]);
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__BN____cmov (param,
    (BArray128.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__BN___cmov <- (trace_h__H__BN___cmov ++ tmp__trace);
    trace_h__H__BN___cmov <-
    (trace_h__H__BN___cmov ++ [(Assert, (BArray128.is_init b_result 0 128))]);
    a <- result;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__BN___cmov);
  }
  proc h__H__BN___cmov_ (a:BArray128.t, b_a:BArray128.t, cond:bool,
                         b:BArray128.t, b_b:BArray128.t) : BArray128.t *
                                                           BArray128.t *
                                                           trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var param:BArray128.t;
    var param_0:bool;
    var param_1:BArray128.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___cmov_:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__BN___cmov_ <- [];
    trace_h__H__BN___cmov_ <-
    (trace_h__H__BN___cmov_ ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__BN___cmov_ <-
    (trace_h__H__BN___cmov_ ++ [(Assert, (BArray128.is_init b_b 0 128))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__BN___cmov (param,
    (BArray128.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__BN___cmov_ <- (trace_h__H__BN___cmov_ ++ tmp__trace);
    trace_h__H__BN___cmov_ <-
    (trace_h__H__BN___cmov_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    a <- result;
    a <- a;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__BN___cmov_);
  }
  proc h__H__BN____fill (a:BArray128.t, b_a:BArray128.t, x:W64.t) : BArray128.t *
                                                                    BArray128.t *
                                                                    trace = {
    var i:int;
    var trace_h__H__BN____fill:trace;
    trace_h__H__BN____fill <- [];
    i <- 0;
    while ((i < 16)) {
      trace_h__H__BN____fill <-
      (trace_h__H__BN____fill ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      b_a <-
      (BArray128.set64d b_a (i * 8) (W64.of_int 18446744073709551615));
      a <- (BArray128.set64 a i x);
      i <- (i + 1);
    }
    return (a, b_a, trace_h__H__BN____fill);
  }
  proc h__H__BN___fill_ (a:BArray128.t, b_a:BArray128.t, x:W64.t) : BArray128.t *
                                                                    BArray128.t *
                                                                    trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:W64.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___fill_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__H__BN___fill_ <- [];
    b_a <- b_a;
    a <- a;
    x <- x;
    b_param <- b_a;
    param <- a;
    param_0 <- x;
    (aux, aux_0, tmp__trace) <@ h__H__BN____fill (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__H__BN___fill_ <- (trace_h__H__BN___fill_ ++ tmp__trace);
    trace_h__H__BN___fill_ <-
    (trace_h__H__BN___fill_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    a <- result;
    a <- a;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__BN___fill_);
  }
  proc h__H__BN___set0_ (a:BArray128.t, b_a:BArray128.t) : BArray128.t *
                                                           BArray128.t *
                                                           trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var t:W64.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:W64.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___set0_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__H__BN___set0_ <- [];
    t <- (W64.of_int 0);
    b_param <- b_a;
    param <- a;
    param_0 <- t;
    (aux, aux_0, tmp__trace) <@ h__H__BN___fill_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__H__BN___set0_ <- (trace_h__H__BN___set0_ ++ tmp__trace);
    trace_h__H__BN___set0_ <-
    (trace_h__H__BN___set0_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    a <- result;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__BN___set0_);
  }
  proc h__H__BN____addc1 (r:BArray128.t, b_r:BArray128.t, a:BArray128.t,
                          b_a:BArray128.t, b:BArray128.t, b_b:BArray128.t,
                          cf:bool) : bool * BArray128.t * BArray128.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__H__BN____addc1:trace;
    trace_h__H__BN____addc1 <- [];
    trace_h__H__BN____addc1 <-
    (trace_h__H__BN____addc1 ++
    [(Assert,
     (((BArray128.is_init b_r 0 8) /\ (BArray128.is_init b_a 0 128)) /\
     (BArray128.is_init b_b 0 128)))]);
    i <- 1;
    while ((i < 16)) {
      trace_h__H__BN____addc1 <-
      (trace_h__H__BN____addc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      t <- (BArray128.get64 a i);
      trace_h__H__BN____addc1 <-
      (trace_h__H__BN____addc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      (cf, t) <- (adc_64 t (BArray128.get64 b i) cf);
      trace_h__H__BN____addc1 <-
      (trace_h__H__BN____addc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      b_r <-
      (BArray128.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray128.set64 r i t);
      i <- (i + 1);
    }
    return (cf, r, b_r, trace_h__H__BN____addc1);
  }
  proc h__H__BN___addc1 (r:BArray128.t, b_r:BArray128.t, a:BArray128.t,
                         b_a:BArray128.t, b:BArray128.t, b_b:BArray128.t,
                         cf:bool) : bool * BArray128.t * BArray128.t * trace = {
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux:bool;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___addc1:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__H__BN___addc1 <- [];
    trace_h__H__BN___addc1 <-
    (trace_h__H__BN___addc1 ++
    [(Assert,
     (((BArray128.is_init b_r 0 8) /\ (BArray128.is_init b_a 0 128)) /\
     (BArray128.is_init b_b 0 128)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN____addc1 (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___addc1 <- (trace_h__H__BN___addc1 ++ tmp__trace);
    trace_h__H__BN___addc1 <-
    (trace_h__H__BN___addc1 ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__H__BN___addc1);
  }
  proc h__H__BN___addc1_ (r:BArray128.t, b_r:BArray128.t, a:BArray128.t,
                          b_a:BArray128.t, b:BArray128.t, b_b:BArray128.t,
                          cf:bool) : bool * BArray128.t * BArray128.t * trace = {
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux:bool;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___addc1_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__H__BN___addc1_ <- [];
    trace_h__H__BN___addc1_ <-
    (trace_h__H__BN___addc1_ ++
    [(Assert,
     (((BArray128.is_init b_r 0 8) /\ (BArray128.is_init b_a 0 128)) /\
     (BArray128.is_init b_b 0 128)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___addc1 (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___addc1_ <- (trace_h__H__BN___addc1_ ++ tmp__trace);
    trace_h__H__BN___addc1_ <-
    (trace_h__H__BN___addc1_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    cf <- result;
    r <- result_0;
    r <- r;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__H__BN___addc1_);
  }
  proc h__H__BN___add_ (r:BArray128.t, b_r:BArray128.t, a:BArray128.t,
                        b_a:BArray128.t, b:BArray128.t, b_b:BArray128.t) : 
  bool * BArray128.t * BArray128.t * trace = {
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux:bool;
    var t:W64.t;
    var cf:bool;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___add_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__H__BN___add_ <- [];
    trace_h__H__BN___add_ <-
    (trace_h__H__BN___add_ ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    t <- (BArray128.get64 a 0);
    (cf, t) <- (adc_64 t (BArray128.get64 b 0) false);
    b_r <- (BArray128.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray128.set64 r 0 t);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___addc1_ (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___add_ <- (trace_h__H__BN___add_ ++ tmp__trace);
    trace_h__H__BN___add_ <-
    (trace_h__H__BN___add_ ++ [(Assert, (BArray128.is_init b_result 0 128))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__H__BN___add_);
  }
  proc h__H__BN____subc1U (a:BArray128.t, b_a:BArray128.t, b:BArray128.t,
                           b_b:BArray128.t, cf:bool) : bool * BArray128.t *
                                                       BArray128.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var i:int;
    var t:W64.t;
    var trace_h__H__BN____subc1U:trace;
    trace_h__H__BN____subc1U <- [];
    trace_h__H__BN____subc1U <-
    (trace_h__H__BN____subc1U ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__BN____subc1U <-
    (trace_h__H__BN____subc1U ++ [(Assert, (BArray128.is_init b_b 0 128))]);
    i <- 1;
    while ((i < 16)) {
      trace_h__H__BN____subc1U <-
      (trace_h__H__BN____subc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      t <- (BArray128.get64 b i);
      trace_h__H__BN____subc1U <-
      (trace_h__H__BN____subc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      trace_h__H__BN____subc1U <-
      (trace_h__H__BN____subc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      (aux, aux_0) <- (sbb_64 (BArray128.get64 a i) t cf);
      cf <- aux;
      a <- (BArray128.set64 a i aux_0);
      i <- (i + 1);
    }
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__H__BN____subc1U);
  }
  proc h__H__BN___subc1U (a:BArray128.t, b_a:BArray128.t, b:BArray128.t,
                          b_b:BArray128.t, cf:bool) : bool * BArray128.t *
                                                      BArray128.t * trace = {
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux:bool;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___subc1U:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__H__BN___subc1U <- [];
    trace_h__H__BN___subc1U <-
    (trace_h__H__BN___subc1U ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__BN___subc1U <-
    (trace_h__H__BN___subc1U ++ [(Assert, (BArray128.is_init b_b 0 128))]);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN____subc1U (param,
    (BArray128.init_arr (W8.of_int 255)), param_0,
    (BArray128.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___subc1U <- (trace_h__H__BN___subc1U ++ tmp__trace);
    trace_h__H__BN___subc1U <-
    (trace_h__H__BN___subc1U ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__H__BN___subc1U);
  }
  proc h__H__BN___subc1U_ (a:BArray128.t, b_a:BArray128.t, b:BArray128.t,
                           b_b:BArray128.t, cf:bool) : bool * BArray128.t *
                                                       BArray128.t * trace = {
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux:bool;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___subc1U_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__H__BN___subc1U_ <- [];
    trace_h__H__BN___subc1U_ <-
    (trace_h__H__BN___subc1U_ ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__BN___subc1U_ <-
    (trace_h__H__BN___subc1U_ ++ [(Assert, (BArray128.is_init b_b 0 128))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___subc1U (param,
    (BArray128.init_arr (W8.of_int 255)), param_0,
    (BArray128.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___subc1U_ <- (trace_h__H__BN___subc1U_ ++ tmp__trace);
    trace_h__H__BN___subc1U_ <-
    (trace_h__H__BN___subc1U_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    cf <- result;
    a <- result_0;
    a <- a;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__H__BN___subc1U_);
  }
  proc h__H__BN___subU_ (a:BArray128.t, b_a:BArray128.t, b:BArray128.t,
                         b_b:BArray128.t) : bool * BArray128.t *
                                            BArray128.t * trace = {
    var aux_2:BArray128.t;
    var aux_3:BArray128.t;
    var aux_0:W64.t;
    var aux:bool;
    var aux_1:bool;
    var t:W64.t;
    var cf:bool;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___subU_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__H__BN___subU_ <- [];
    trace_h__H__BN___subU_ <-
    (trace_h__H__BN___subU_ ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__BN___subU_ <-
    (trace_h__H__BN___subU_ ++ [(Assert, (BArray128.is_init b_b 0 128))]);
    t <- (BArray128.get64 b 0);
    (aux, aux_0) <- (sbb_64 (BArray128.get64 a 0) t false);
    cf <- aux;
    a <- (BArray128.set64 a 0 aux_0);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux_1, aux_2, aux_3, tmp__trace) <@ h__H__BN___subc1U_ (param,
    (BArray128.init_arr (W8.of_int 255)), param_0,
    (BArray128.init_arr (W8.of_int 255)), param_1);
    result <- aux_1;
    result_0 <- aux_2;
    b_result <- aux_3;
    trace_h__H__BN___subU_ <- (trace_h__H__BN___subU_ ++ tmp__trace);
    trace_h__H__BN___subU_ <-
    (trace_h__H__BN___subU_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__H__BN___subU_);
  }
  proc h__H__BN____negc1 (r:BArray128.t, b_r:BArray128.t, a:BArray128.t,
                          b_a:BArray128.t, cf:bool) : bool * BArray128.t *
                                                      BArray128.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__H__BN____negc1:trace;
    trace_h__H__BN____negc1 <- [];
    trace_h__H__BN____negc1 <-
    (trace_h__H__BN____negc1 ++
    [(Assert, ((BArray128.is_init b_r 0 8) /\ (BArray128.is_init b_a 0 128)))]);
    i <- 1;
    while ((i < 16)) {
      t <- (W64.of_int 0);
      trace_h__H__BN____negc1 <-
      (trace_h__H__BN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      (cf, t) <- (sbb_64 t (BArray128.get64 a i) cf);
      trace_h__H__BN____negc1 <-
      (trace_h__H__BN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      b_r <-
      (BArray128.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray128.set64 r i t);
      i <- (i + 1);
    }
    return (cf, r, b_r, trace_h__H__BN____negc1);
  }
  proc h__H__BN___negc1 (r:BArray128.t, b_r:BArray128.t, a:BArray128.t,
                         b_a:BArray128.t, cf:bool) : bool * BArray128.t *
                                                     BArray128.t * trace = {
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux:bool;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___negc1:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__H__BN___negc1 <- [];
    trace_h__H__BN___negc1 <-
    (trace_h__H__BN___negc1 ++
    [(Assert, ((BArray128.is_init b_r 0 8) /\ (BArray128.is_init b_a 0 128)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN____negc1 (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___negc1 <- (trace_h__H__BN___negc1 ++ tmp__trace);
    trace_h__H__BN___negc1 <-
    (trace_h__H__BN___negc1 ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__H__BN___negc1);
  }
  proc h__H__BN___negc1_ (r:BArray128.t, b_r:BArray128.t, a:BArray128.t,
                          b_a:BArray128.t, cf:bool) : bool * BArray128.t *
                                                      BArray128.t * trace = {
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux:bool;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___negc1_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__H__BN___negc1_ <- [];
    trace_h__H__BN___negc1_ <-
    (trace_h__H__BN___negc1_ ++
    [(Assert, ((BArray128.is_init b_r 0 8) /\ (BArray128.is_init b_a 0 128)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___negc1 (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___negc1_ <- (trace_h__H__BN___negc1_ ++ tmp__trace);
    trace_h__H__BN___negc1_ <-
    (trace_h__H__BN___negc1_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    cf <- result;
    r <- result_0;
    r <- r;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__H__BN___negc1_);
  }
  proc h__H__BN___neg_ (r:BArray128.t, b_r:BArray128.t, a:BArray128.t,
                        b_a:BArray128.t) : bool * BArray128.t * BArray128.t *
                                           trace = {
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux:bool;
    var t:W64.t;
    var cf:bool;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__BN___neg_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__H__BN___neg_ <- [];
    trace_h__H__BN___neg_ <-
    (trace_h__H__BN___neg_ ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    t <- (W64.of_int 0);
    (cf, t) <- (sbb_64 t (BArray128.get64 a 0) false);
    b_r <- (BArray128.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray128.set64 r 0 t);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___negc1_ (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___neg_ <- (trace_h__H__BN___neg_ ++ tmp__trace);
    trace_h__H__BN___neg_ <-
    (trace_h__H__BN___neg_ ++ [(Assert, (BArray128.is_init b_result 0 128))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__H__BN___neg_);
  }
  proc h__H__BN___caddU_ (x:BArray128.t, b_x:BArray128.t, cf:bool,
                          y:BArray128.t, b_y:BArray128.t) : BArray128.t *
                                                            BArray128.t *
                                                            trace = {
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux_2:BArray128.t;
    var aux_3:BArray128.t;
    var aux:bool;
    var b__tmp:BArray128.t;
    var param:bool;
    var result:W64.t;
    var mask:W64.t;
    var b_tmp:BArray128.t;
    var tmp:BArray128.t;
    var _tmp:BArray128.t;
    var b_param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var param_2:BArray128.t;
    var result_0:bool;
    var result_1:BArray128.t;
    var b_result:BArray128.t;
    var param_3:W64.t;
    var result_2:bool;
    var param_4:BArray128.t;
    var param_5:bool;
    var param_6:BArray128.t;
    var result_3:BArray128.t;
    var b_result_0:BArray128.t;
    var trace_h__H__BN___caddU_:trace;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    param_6 <- witness;
    result_1 <- witness;
    result_3 <- witness;
    tmp <- witness;
    trace_h__H__BN___caddU_ <- [];
    trace_h__H__BN___caddU_ <-
    (trace_h__H__BN___caddU_ ++ [(Assert, (BArray128.is_init b_x 0 128))]);
    trace_h__H__BN___caddU_ <-
    (trace_h__H__BN___caddU_ ++ [(Assert, (BArray128.is_init b_y 0 128))]);
    b__tmp <- (BArray128.init_arr (W8.of_int 0));
    param <- cf;
    (result, tmp__trace) <@ uTIL____cf_mask (param);
    trace_h__H__BN___caddU_ <- (trace_h__H__BN___caddU_ ++ tmp__trace);
    mask <- result;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param_0 <- tmp;
    param_1 <- x;
    param_2 <- y;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___add_ (param_0, b_param,
    param_1, (BArray128.init_arr (W8.of_int 255)), param_2,
    (BArray128.init_arr (W8.of_int 255)));
    result_0 <- aux;
    result_1 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___caddU_ <- (trace_h__H__BN___caddU_ ++ tmp__trace);
    trace_h__H__BN___caddU_ <-
    (trace_h__H__BN___caddU_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    tmp <- result_1;
    param_3 <- mask;
    (result_2, tmp__trace) <@ uTIL____mask_cf (param_3);
    trace_h__H__BN___caddU_ <- (trace_h__H__BN___caddU_ ++ tmp__trace);
    cf <- result_2;
    param_4 <- x;
    param_5 <- cf;
    param_6 <- tmp;
    (aux_2, aux_3, tmp__trace) <@ h__H__BN___cmov_ (param_4,
    (BArray128.init_arr (W8.of_int 255)), param_5, param_6,
    (BArray128.init_arr (W8.of_int 255)));
    result_3 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__H__BN___caddU_ <- (trace_h__H__BN___caddU_ ++ tmp__trace);
    trace_h__H__BN___caddU_ <-
    (trace_h__H__BN___caddU_ ++
    [(Assert, (BArray128.is_init b_result_0 0 128))]);
    x <- result_3;
    b_x <- (BArray128.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__H__BN___caddU_);
  }
  proc h__H__BN___cminusP_ (x:BArray128.t, b_x:BArray128.t, mP:BArray128.t,
                            b_mP:BArray128.t, lastbit:W64.t) : BArray128.t *
                                                               BArray128.t *
                                                               trace = {
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux_2:BArray128.t;
    var aux_3:BArray128.t;
    var aux:bool;
    var b__tmp:BArray128.t;
    var b_tmp:BArray128.t;
    var tmp:BArray128.t;
    var _tmp:BArray128.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var result:bool;
    var result_0:BArray128.t;
    var b_result:BArray128.t;
    var _cf:bool;
    var param_2:BArray128.t;
    var param_3:bool;
    var param_4:BArray128.t;
    var result_1:BArray128.t;
    var b_result_0:BArray128.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:W64.t;
    var trace_h__H__BN___cminusP_:trace;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    result_0 <- witness;
    result_1 <- witness;
    tmp <- witness;
    trace_h__H__BN___cminusP_ <- [];
    trace_h__H__BN___cminusP_ <-
    (trace_h__H__BN___cminusP_ ++ [(Assert, (BArray128.is_init b_x 0 128))]);
    trace_h__H__BN___cminusP_ <-
    (trace_h__H__BN___cminusP_ ++ [(Assert, (BArray128.is_init b_mP 0 128))]);
    b__tmp <- (BArray128.init_arr (W8.of_int 0));
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- x;
    param_1 <- mP;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___add_ (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___cminusP_ <- (trace_h__H__BN___cminusP_ ++ tmp__trace);
    trace_h__H__BN___cminusP_ <-
    (trace_h__H__BN___cminusP_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    _cf <- result;
    tmp <- result_0;
    ( _0, lastbit) <- (adc_64 lastbit (W64.of_int 0) _cf);
    ( _1, _cf,  _2,  _3,  _4,  _5) <- (NEG_64 lastbit);
    param_2 <- x;
    param_3 <- _cf;
    param_4 <- tmp;
    (aux_2, aux_3, tmp__trace) <@ h__H__BN___cmov_ (param_2,
    (BArray128.init_arr (W8.of_int 255)), param_3, param_4,
    (BArray128.init_arr (W8.of_int 255)));
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__H__BN___cminusP_ <- (trace_h__H__BN___cminusP_ ++ tmp__trace);
    trace_h__H__BN___cminusP_ <-
    (trace_h__H__BN___cminusP_ ++
    [(Assert, (BArray128.is_init b_result_0 0 128))]);
    x <- result_1;
    b_x <- (BArray128.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__H__BN___cminusP_);
  }
  proc h__H__MUL__UNR____muln_innerloop (x:BArray24.t, b_x:BArray24.t, k:int,
                                         istart:int, iend:int, a:BArray128.t,
                                         b_a:BArray128.t, b:BArray128.t,
                                         b_b:BArray128.t) : BArray24.t *
                                                            BArray24.t *
                                                            trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var inc:int;
    var i:int;
    var j:int;
    var t0:W64.t;
    var t1:W64.t;
    var param:BArray24.t;
    var param_0:W64.t;
    var param_1:W64.t;
    var param_2:int;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var trace_h__H__MUL__UNR____muln_innerloop:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__H__MUL__UNR____muln_innerloop <- [];
    trace_h__H__MUL__UNR____muln_innerloop <-
    (trace_h__H__MUL__UNR____muln_innerloop ++
    [(Assert,
     (((((((0 <= istart) /\ (iend <= 16)) /\ (0 <= (k - (iend - 1)))) /\
        ((k - istart) < 16)) /\
       (BArray24.is_init b_x 0 24)) /\
      (BArray128.is_init b_a (8 * istart) (8 * (iend - istart)))) /\
     (BArray128.is_init b_b 0 128)))]);
    inc <- iend;
    i <- istart;
    while ((i < inc)) {
      j <- (k - i);
      trace_h__H__MUL__UNR____muln_innerloop <-
      (trace_h__H__MUL__UNR____muln_innerloop ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      trace_h__H__MUL__UNR____muln_innerloop <-
      (trace_h__H__MUL__UNR____muln_innerloop ++
      [(Assert, (BArray128.is_init b_a (i * 8) 8))]);
      t0 <- (BArray128.get64 a i);
      trace_h__H__MUL__UNR____muln_innerloop <-
      (trace_h__H__MUL__UNR____muln_innerloop ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 128)))]);
      (t1, t0) <- (mulu_64 t0 (BArray128.get64 b j));
      param <- x;
      param_0 <- t1;
      param_1 <- t0;
      param_2 <- k;
      (aux, aux_0, tmp__trace) <@ uTIL____addacc3 (param,
      (BArray24.init_arr (W8.of_int 255)), param_0, param_1, param_2);
      result <- aux;
      b_result <- aux_0;
      trace_h__H__MUL__UNR____muln_innerloop <-
      (trace_h__H__MUL__UNR____muln_innerloop ++ tmp__trace);
      trace_h__H__MUL__UNR____muln_innerloop <-
      (trace_h__H__MUL__UNR____muln_innerloop ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      x <- result;
      i <- (i + 1);
    }
    b_x <- (BArray24.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__H__MUL__UNR____muln_innerloop);
  }
  proc h__H__MUL__UNR____ps_muln (r:BArray256.t, b_r:BArray256.t,
                                  a:BArray128.t, b_a:BArray128.t,
                                  b:BArray128.t, b_b:BArray128.t) : BArray256.t *
                                                                    BArray256.t *
                                                                    trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var aux_1:BArray24.t;
    var aux_2:BArray24.t;
    var inc:int;
    var b_x:BArray24.t;
    var t0:W64.t;
    var t1:W64.t;
    var x:BArray24.t;
    var k:int;
    var b_param:BArray24.t;
    var param:BArray24.t;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var param_3:BArray128.t;
    var param_4:BArray128.t;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var b_param_0:BArray24.t;
    var param_5:BArray24.t;
    var param_6:int;
    var param_7:int;
    var param_8:int;
    var param_9:BArray128.t;
    var param_10:BArray128.t;
    var result_0:BArray24.t;
    var b_result_0:BArray24.t;
    var trace_h__H__MUL__UNR____ps_muln:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_x <- witness;
    param <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_9 <- witness;
    param_10 <- witness;
    result <- witness;
    result_0 <- witness;
    x <- witness;
    trace_h__H__MUL__UNR____ps_muln <- [];
    trace_h__H__MUL__UNR____ps_muln <-
    (trace_h__H__MUL__UNR____ps_muln ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    b_x <- (BArray24.init_arr (W8.of_int 0));
    t0 <- (BArray128.get64 a 0);
    (t1, t0) <- (mulu_64 t0 (BArray128.get64 b 0));
    b_r <- (BArray256.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 0 t0);
    b_x <- (BArray24.set64d b_x 8 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 1 t1);
    b_x <- (BArray24.set64d b_x 16 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 2 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 0 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 0 (W64.of_int 0));
    k <- 1;
    while ((k < 16)) {
      b_param <- b_x;
      param <- x;
      param_0 <- k;
      param_1 <- 0;
      param_2 <- (k + 1);
      param_3 <- a;
      param_4 <- b;
      (aux, aux_0, tmp__trace) <@ h__H__MUL__UNR____muln_innerloop (param,
      b_param, param_0, param_1, param_2, param_3,
      (BArray128.init_arr (W8.of_int 255)), param_4,
      (BArray128.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__H__MUL__UNR____ps_muln <-
      (trace_h__H__MUL__UNR____ps_muln ++ tmp__trace);
      trace_h__H__MUL__UNR____ps_muln <-
      (trace_h__H__MUL__UNR____ps_muln ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result;
      trace_h__H__MUL__UNR____ps_muln <-
      (trace_h__H__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__H__MUL__UNR____ps_muln <-
      (trace_h__H__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__H__MUL__UNR____ps_muln <-
      (trace_h__H__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r k t0);
      k <- (k + 1);
    }
    inc <- ((2 * 16) - 1);
    k <- 16;
    while ((k < inc)) {
      b_param_0 <- b_x;
      param_5 <- x;
      param_6 <- k;
      param_7 <- ((k - 16) + 1);
      param_8 <- 16;
      param_9 <- a;
      param_10 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__H__MUL__UNR____muln_innerloop (
      param_5, b_param_0, param_6, param_7, param_8, param_9,
      (BArray128.init_arr (W8.of_int 255)), param_10,
      (BArray128.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__H__MUL__UNR____ps_muln <-
      (trace_h__H__MUL__UNR____ps_muln ++ tmp__trace);
      trace_h__H__MUL__UNR____ps_muln <-
      (trace_h__H__MUL__UNR____ps_muln ++
      [(Assert, (BArray24.is_init b_result_0 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_0;
      trace_h__H__MUL__UNR____ps_muln <-
      (trace_h__H__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__H__MUL__UNR____ps_muln <-
      (trace_h__H__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__H__MUL__UNR____ps_muln <-
      (trace_h__H__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r k t0);
      k <- (k + 1);
    }
    trace_h__H__MUL__UNR____ps_muln <-
    (trace_h__H__MUL__UNR____ps_muln ++
    [(Assert,
     ((0 <= (((2 * 16) - 1) * 8)) /\ (((((2 * 16) - 1) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__UNR____ps_muln <-
    (trace_h__H__MUL__UNR____ps_muln ++
    [(Assert,
     ((0 <= ((((2 * 16) - 1) %% 3) * 8)) /\
     ((((((2 * 16) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__H__MUL__UNR____ps_muln <-
    (trace_h__H__MUL__UNR____ps_muln ++
    [(Assert, (BArray24.is_init b_x ((((2 * 16) - 1) %% 3) * 8) 8))]);
    b_r <-
    (BArray256.set64d b_r (((2 * 16) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <-
    (BArray256.set64 r ((2 * 16) - 1)
    (BArray24.get64 x (((2 * 16) - 1) %% 3)));
    return (r, b_r, trace_h__H__MUL__UNR____ps_muln);
  }
  proc h__H__MUL__UNR___ps_muln (r:BArray256.t, b_r:BArray256.t,
                                 a:BArray128.t, b_a:BArray128.t,
                                 b:BArray128.t, b_b:BArray128.t) : BArray256.t *
                                                                   BArray256.t *
                                                                   trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__MUL__UNR___ps_muln:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__MUL__UNR___ps_muln <- [];
    trace_h__H__MUL__UNR___ps_muln <-
    (trace_h__H__MUL__UNR___ps_muln ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__UNR____ps_muln (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__UNR___ps_muln <-
    (trace_h__H__MUL__UNR___ps_muln ++ tmp__trace);
    trace_h__H__MUL__UNR___ps_muln <-
    (trace_h__H__MUL__UNR___ps_muln ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__UNR___ps_muln);
  }
  proc h__H__MUL__UNR___ps_muln_ (r:BArray256.t, b_r:BArray256.t,
                                  a:BArray128.t, b_a:BArray128.t,
                                  b:BArray128.t, b_b:BArray128.t) : BArray256.t *
                                                                    BArray256.t *
                                                                    trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__MUL__UNR___ps_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__MUL__UNR___ps_muln_ <- [];
    trace_h__H__MUL__UNR___ps_muln_ <-
    (trace_h__H__MUL__UNR___ps_muln_ ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__UNR___ps_muln (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__UNR___ps_muln_ <-
    (trace_h__H__MUL__UNR___ps_muln_ ++ tmp__trace);
    trace_h__H__MUL__UNR___ps_muln_ <-
    (trace_h__H__MUL__UNR___ps_muln_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__UNR___ps_muln_);
  }
  proc h__H__MUL__UNR____sqrn_innerloop (x:BArray24.t, b_x:BArray24.t, k:int,
                                         istart:int, iend:int, a:BArray128.t,
                                         b_a:BArray128.t) : BArray24.t *
                                                            BArray24.t *
                                                            trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var inc:int;
    var i:int;
    var j:int;
    var ti:W64.t;
    var tj:W64.t;
    var param:BArray24.t;
    var param_0:W64.t;
    var param_1:W64.t;
    var param_2:int;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var trace_h__H__MUL__UNR____sqrn_innerloop:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__H__MUL__UNR____sqrn_innerloop <- [];
    trace_h__H__MUL__UNR____sqrn_innerloop <-
    (trace_h__H__MUL__UNR____sqrn_innerloop ++
    [(Assert,
     ((((((0 <= istart) /\ (iend <= 16)) /\ (0 <= (k - (iend - 1)))) /\
       ((k - istart) < 16)) /\
      (BArray24.is_init b_x 0 24)) /\
     (BArray128.is_init b_a 0 128)))]);
    inc <- iend;
    i <- istart;
    while ((i < inc)) {
      j <- (k - i);
      trace_h__H__MUL__UNR____sqrn_innerloop <-
      (trace_h__H__MUL__UNR____sqrn_innerloop ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      ti <- (BArray128.get64 a i);
      trace_h__H__MUL__UNR____sqrn_innerloop <-
      (trace_h__H__MUL__UNR____sqrn_innerloop ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 128)))]);
      tj <- (BArray128.get64 a j);
      param <- x;
      param_0 <- ti;
      param_1 <- tj;
      param_2 <- k;
      (aux, aux_0, tmp__trace) <@ uTIL____addacc3x2 (param,
      (BArray24.init_arr (W8.of_int 255)), param_0, param_1, param_2);
      result <- aux;
      b_result <- aux_0;
      trace_h__H__MUL__UNR____sqrn_innerloop <-
      (trace_h__H__MUL__UNR____sqrn_innerloop ++ tmp__trace);
      trace_h__H__MUL__UNR____sqrn_innerloop <-
      (trace_h__H__MUL__UNR____sqrn_innerloop ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      x <- result;
      i <- (i + 1);
    }
    b_x <- (BArray24.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__H__MUL__UNR____sqrn_innerloop);
  }
  proc h__H__MUL__UNR____ps_sqrn (r:BArray256.t, b_r:BArray256.t,
                                  a:BArray128.t, b_a:BArray128.t) : BArray256.t *
                                                                    BArray256.t *
                                                                    trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var aux_1:BArray24.t;
    var aux_2:BArray24.t;
    var aux_3:BArray24.t;
    var aux_4:BArray24.t;
    var aux_5:BArray24.t;
    var aux_6:BArray24.t;
    var inc:int;
    var b_x:BArray24.t;
    var t0:W64.t;
    var t1:W64.t;
    var x:BArray24.t;
    var k:int;
    var b_param:BArray24.t;
    var param:BArray24.t;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var param_3:BArray128.t;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var param_4:BArray24.t;
    var param_5:W64.t;
    var param_6:W64.t;
    var param_7:int;
    var result_0:BArray24.t;
    var b_result_0:BArray24.t;
    var b_param_0:BArray24.t;
    var param_8:BArray24.t;
    var param_9:int;
    var param_10:int;
    var param_11:int;
    var param_12:BArray128.t;
    var result_1:BArray24.t;
    var b_result_1:BArray24.t;
    var param_13:BArray24.t;
    var param_14:W64.t;
    var param_15:W64.t;
    var param_16:int;
    var result_2:BArray24.t;
    var b_result_2:BArray24.t;
    var trace_h__H__MUL__UNR____ps_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_x <- witness;
    param <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_8 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    x <- witness;
    trace_h__H__MUL__UNR____ps_sqrn <- [];
    trace_h__H__MUL__UNR____ps_sqrn <-
    (trace_h__H__MUL__UNR____ps_sqrn ++
    [(Assert, (BArray128.is_init b_a 0 128))]);
    b_x <- (BArray24.init_arr (W8.of_int 0));
    t0 <- (BArray128.get64 a 0);
    (t1, t0) <- (mulu_64 t0 t0);
    b_r <- (BArray256.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 0 t0);
    b_x <- (BArray24.set64d b_x 8 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 1 t1);
    b_x <- (BArray24.set64d b_x 16 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 2 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 0 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 0 (W64.of_int 0));
    k <- 1;
    while ((k < 16)) {
      b_param <- b_x;
      param <- x;
      param_0 <- k;
      param_1 <- 0;
      param_2 <- ((k + 1) %/ 2);
      param_3 <- a;
      (aux, aux_0, tmp__trace) <@ h__H__MUL__UNR____sqrn_innerloop (param,
      b_param, param_0, param_1, param_2, param_3,
      (BArray128.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__H__MUL__UNR____ps_sqrn <-
      (trace_h__H__MUL__UNR____ps_sqrn ++ tmp__trace);
      trace_h__H__MUL__UNR____ps_sqrn <-
      (trace_h__H__MUL__UNR____ps_sqrn ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result;
      if (((k %% 2) = 0)) {
        trace_h__H__MUL__UNR____ps_sqrn <-
        (trace_h__H__MUL__UNR____ps_sqrn ++
        [(Assert, ((0 <= ((k %/ 2) * 8)) /\ ((((k %/ 2) * 8) + 8) <= 128)))]);
        t0 <- (BArray128.get64 a (k %/ 2));
        (t1, t0) <- (mulu_64 t0 t0);
        param_4 <- x;
        param_5 <- t1;
        param_6 <- t0;
        param_7 <- k;
        (aux_1, aux_2, tmp__trace) <@ uTIL____addacc3 (param_4,
        (BArray24.init_arr (W8.of_int 255)), param_5, param_6, param_7);
        result_0 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__H__MUL__UNR____ps_sqrn <-
        (trace_h__H__MUL__UNR____ps_sqrn ++ tmp__trace);
        trace_h__H__MUL__UNR____ps_sqrn <-
        (trace_h__H__MUL__UNR____ps_sqrn ++
        [(Assert, (BArray24.is_init b_result_0 0 24))]);
        b_x <- (BArray24.init_arr (W8.of_int 255));
        x <- result_0;
      } else {
        
      }
      trace_h__H__MUL__UNR____ps_sqrn <-
      (trace_h__H__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__H__MUL__UNR____ps_sqrn <-
      (trace_h__H__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__H__MUL__UNR____ps_sqrn <-
      (trace_h__H__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r k t0);
      k <- (k + 1);
    }
    inc <- ((2 * 16) - 1);
    k <- 16;
    while ((k < inc)) {
      b_param_0 <- b_x;
      param_8 <- x;
      param_9 <- k;
      param_10 <- ((k - 16) + 1);
      param_11 <- ((k + 1) %/ 2);
      param_12 <- a;
      (aux_3, aux_4, tmp__trace) <@ h__H__MUL__UNR____sqrn_innerloop (
      param_8, b_param_0, param_9, param_10, param_11, param_12,
      (BArray128.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__H__MUL__UNR____ps_sqrn <-
      (trace_h__H__MUL__UNR____ps_sqrn ++ tmp__trace);
      trace_h__H__MUL__UNR____ps_sqrn <-
      (trace_h__H__MUL__UNR____ps_sqrn ++
      [(Assert, (BArray24.is_init b_result_1 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_1;
      if (((k %% 2) = 0)) {
        trace_h__H__MUL__UNR____ps_sqrn <-
        (trace_h__H__MUL__UNR____ps_sqrn ++
        [(Assert, ((0 <= ((k %/ 2) * 8)) /\ ((((k %/ 2) * 8) + 8) <= 128)))]);
        t0 <- (BArray128.get64 a (k %/ 2));
        (t1, t0) <- (mulu_64 t0 t0);
        param_13 <- x;
        param_14 <- t1;
        param_15 <- t0;
        param_16 <- k;
        (aux_5, aux_6, tmp__trace) <@ uTIL____addacc3 (param_13,
        (BArray24.init_arr (W8.of_int 255)), param_14, param_15, param_16);
        result_2 <- aux_5;
        b_result_2 <- aux_6;
        trace_h__H__MUL__UNR____ps_sqrn <-
        (trace_h__H__MUL__UNR____ps_sqrn ++ tmp__trace);
        trace_h__H__MUL__UNR____ps_sqrn <-
        (trace_h__H__MUL__UNR____ps_sqrn ++
        [(Assert, (BArray24.is_init b_result_2 0 24))]);
        b_x <- (BArray24.init_arr (W8.of_int 255));
        x <- result_2;
      } else {
        
      }
      trace_h__H__MUL__UNR____ps_sqrn <-
      (trace_h__H__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__H__MUL__UNR____ps_sqrn <-
      (trace_h__H__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__H__MUL__UNR____ps_sqrn <-
      (trace_h__H__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r k t0);
      k <- (k + 1);
    }
    trace_h__H__MUL__UNR____ps_sqrn <-
    (trace_h__H__MUL__UNR____ps_sqrn ++
    [(Assert,
     ((0 <= (((2 * 16) - 1) * 8)) /\ (((((2 * 16) - 1) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__UNR____ps_sqrn <-
    (trace_h__H__MUL__UNR____ps_sqrn ++
    [(Assert,
     ((0 <= ((((2 * 16) - 1) %% 3) * 8)) /\
     ((((((2 * 16) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__H__MUL__UNR____ps_sqrn <-
    (trace_h__H__MUL__UNR____ps_sqrn ++
    [(Assert, (BArray24.is_init b_x ((((2 * 16) - 1) %% 3) * 8) 8))]);
    b_r <-
    (BArray256.set64d b_r (((2 * 16) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <-
    (BArray256.set64 r ((2 * 16) - 1)
    (BArray24.get64 x (((2 * 16) - 1) %% 3)));
    return (r, b_r, trace_h__H__MUL__UNR____ps_sqrn);
  }
  proc h__H__MUL__UNR___ps_sqrn (r:BArray256.t, b_r:BArray256.t,
                                 a:BArray128.t, b_a:BArray128.t) : BArray256.t *
                                                                   BArray256.t *
                                                                   trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__MUL__UNR___ps_sqrn:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__H__MUL__UNR___ps_sqrn <- [];
    trace_h__H__MUL__UNR___ps_sqrn <-
    (trace_h__H__MUL__UNR___ps_sqrn ++
    [(Assert, (BArray128.is_init b_a 0 128))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__UNR____ps_sqrn (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__UNR___ps_sqrn <-
    (trace_h__H__MUL__UNR___ps_sqrn ++ tmp__trace);
    trace_h__H__MUL__UNR___ps_sqrn <-
    (trace_h__H__MUL__UNR___ps_sqrn ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__UNR___ps_sqrn);
  }
  proc h__H__MUL__UNR___ps_sqrn_ (r:BArray256.t, b_r:BArray256.t,
                                  a:BArray128.t, b_a:BArray128.t) : BArray256.t *
                                                                    BArray256.t *
                                                                    trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__MUL__UNR___ps_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__H__MUL__UNR___ps_sqrn_ <- [];
    trace_h__H__MUL__UNR___ps_sqrn_ <-
    (trace_h__H__MUL__UNR___ps_sqrn_ ++
    [(Assert, (BArray128.is_init b_a 0 128))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__UNR___ps_sqrn (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__UNR___ps_sqrn_ <-
    (trace_h__H__MUL__UNR___ps_sqrn_ ++ tmp__trace);
    trace_h__H__MUL__UNR___ps_sqrn_ <-
    (trace_h__H__MUL__UNR___ps_sqrn_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__UNR___ps_sqrn_);
  }
  proc h__H__MUL__UNR____mont_redM (r:BArray128.t, b_r:BArray128.t,
                                    a:BArray256.t, b_a:BArray256.t,
                                    _P_mP:BArray256.t, b__P_mP:BArray256.t,
                                    _U0:W64.t) : BArray128.t * BArray128.t *
                                                 trace = {
    var aux_11:BArray128.t;
    var aux_12:BArray128.t;
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var aux_1:BArray24.t;
    var aux_2:BArray24.t;
    var aux_3:BArray24.t;
    var aux_4:BArray24.t;
    var aux_5:BArray24.t;
    var aux_6:BArray24.t;
    var aux_7:BArray24.t;
    var aux_8:BArray24.t;
    var aux_10:W64.t;
    var aux_9:bool;
    var inc:int;
    var b_x:BArray24.t;
    var x:BArray24.t;
    var b_P:BArray128.t;
    var p:BArray128.t;
    var k:int;
    var b_param:BArray24.t;
    var param:BArray24.t;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var b_param_0:BArray128.t;
    var param_3:BArray128.t;
    var b_param_1:BArray128.t;
    var param_4:BArray128.t;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var zero:W64.t;
    var t0:W64.t;
    var param_5:BArray24.t;
    var param_6:W64.t;
    var param_7:W64.t;
    var param_8:int;
    var result_0:BArray24.t;
    var b_result_0:BArray24.t;
    var t1:W64.t;
    var param_9:BArray24.t;
    var param_10:W64.t;
    var param_11:W64.t;
    var param_12:int;
    var result_1:BArray24.t;
    var b_result_1:BArray24.t;
    var b_param_2:BArray24.t;
    var param_13:BArray24.t;
    var param_14:int;
    var param_15:int;
    var param_16:int;
    var b_param_3:BArray128.t;
    var param_17:BArray128.t;
    var b_param_4:BArray128.t;
    var param_18:BArray128.t;
    var result_2:BArray24.t;
    var b_result_2:BArray24.t;
    var param_19:BArray24.t;
    var param_20:W64.t;
    var param_21:W64.t;
    var param_22:int;
    var result_3:BArray24.t;
    var b_result_3:BArray24.t;
    var lastbit:W64.t;
    var cf:bool;
    var b_mP:BArray128.t;
    var mP:BArray128.t;
    var b_param_5:BArray128.t;
    var param_23:BArray128.t;
    var b_param_6:BArray128.t;
    var param_24:BArray128.t;
    var param_25:W64.t;
    var result_4:BArray128.t;
    var b_result_4:BArray128.t;
    var  _0:W64.t;
    var  _1:bool;
    var trace_h__H__MUL__UNR____mont_redM:trace;
    p <- witness;
    b_P <- witness;
    b_mP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_x <- witness;
    mP <- witness;
    param <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_9 <- witness;
    param_13 <- witness;
    param_17 <- witness;
    param_18 <- witness;
    param_19 <- witness;
    param_23 <- witness;
    param_24 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_4 <- witness;
    x <- witness;
    trace_h__H__MUL__UNR____mont_redM <- [];
    trace_h__H__MUL__UNR____mont_redM <-
    (trace_h__H__MUL__UNR____mont_redM ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b__P_mP 0 256)))]);
    b_x <- (BArray24.init_arr (W8.of_int 0));
    b_x <- (BArray24.set64d b_x 0 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 0 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 8 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 1 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 16 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 2 (W64.of_int 0));
    b_P <- (SBArray256_128.get_sub64 b__P_mP 0);
    p <- (SBArray256_128.get_sub64 _P_mP 0);
    k <- 0;
    while ((k < 16)) {
      b_param <- b_x;
      param <- x;
      param_0 <- k;
      param_1 <- 0;
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      b_param_1 <- b_P;
      param_4 <- p;
      (aux, aux_0, tmp__trace) <@ h__H__MUL__UNR____muln_innerloop (param,
      b_param, param_0, param_1, param_2, param_3, b_param_0, param_4,
      b_param_1);
      result <- aux;
      b_result <- aux_0;
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      x <- result;
      zero <- (W64.of_int 0);
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      t0 <- (BArray256.get64 a k);
      param_5 <- x;
      param_6 <- zero;
      param_7 <- t0;
      param_8 <- k;
      (aux_1, aux_2, tmp__trace) <@ uTIL____addacc3 (param_5,
      (BArray24.init_arr (W8.of_int 255)), param_6, param_7, param_8);
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result_0 0 24))]);
      x <- result_0;
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      ( _0, t0) <- (mulu_64 t0 _U0);
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 128)))]);
      b_r <-
      (BArray128.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray128.set64 r k t0);
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++
      [(Assert, (BArray128.is_init b_P 0 8))]);
      (t1, t0) <- (mulu_64 t0 (BArray128.get64 p 0));
      param_9 <- x;
      param_10 <- t1;
      param_11 <- t0;
      param_12 <- k;
      (aux_3, aux_4, tmp__trace) <@ uTIL____addacc3 (param_9,
      (BArray24.init_arr (W8.of_int 255)), param_10, param_11, param_12);
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result_1 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_1;
      k <- (k + 1);
    }
    inc <- ((2 * 16) - 1);
    k <- 16;
    while ((k < inc)) {
      b_param_2 <- b_x;
      param_13 <- x;
      param_14 <- k;
      param_15 <- ((k - 16) + 1);
      param_16 <- 16;
      b_param_3 <- b_r;
      param_17 <- r;
      b_param_4 <- b_P;
      param_18 <- p;
      (aux_5, aux_6, tmp__trace) <@ h__H__MUL__UNR____muln_innerloop (
      param_13, b_param_2, param_14, param_15, param_16, param_17, b_param_3,
      param_18, b_param_4);
      result_2 <- aux_5;
      b_result_2 <- aux_6;
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result_2 0 24))]);
      x <- result_2;
      zero <- (W64.of_int 0);
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      t0 <- (BArray256.get64 a k);
      param_19 <- x;
      param_20 <- zero;
      param_21 <- t0;
      param_22 <- k;
      (aux_7, aux_8, tmp__trace) <@ uTIL____addacc3 (param_19,
      (BArray24.init_arr (W8.of_int 255)), param_20, param_21, param_22);
      result_3 <- aux_7;
      b_result_3 <- aux_8;
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result_3 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_3;
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= ((k - 16) * 8)) /\ ((((k - 16) * 8) + 8) <= 128)))]);
      b_r <-
      (BArray128.set64d b_r ((k - 16) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray128.set64 r (k - 16) t0);
      trace_h__H__MUL__UNR____mont_redM <-
      (trace_h__H__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      k <- (k + 1);
    }
    trace_h__H__MUL__UNR____mont_redM <-
    (trace_h__H__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= (((2 * 16) %% 3) * 8)) /\ (((((2 * 16) %% 3) * 8) + 8) <= 24)))]);
    trace_h__H__MUL__UNR____mont_redM <-
    (trace_h__H__MUL__UNR____mont_redM ++
    [(Assert, (BArray24.is_init b_x (((2 * 16) %% 3) * 8) 8))]);
    lastbit <- (BArray24.get64 x ((2 * 16) %% 3));
    trace_h__H__MUL__UNR____mont_redM <-
    (trace_h__H__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= ((((2 * 16) - 1) %% 3) * 8)) /\
     ((((((2 * 16) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__H__MUL__UNR____mont_redM <-
    (trace_h__H__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= ((((2 * 16) - 1) %% 3) * 8)) /\
     ((((((2 * 16) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__H__MUL__UNR____mont_redM <-
    (trace_h__H__MUL__UNR____mont_redM ++
    [(Assert, (BArray24.is_init b_x ((((2 * 16) - 1) %% 3) * 8) 8))]);
    trace_h__H__MUL__UNR____mont_redM <-
    (trace_h__H__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= (((2 * 16) - 1) * 8)) /\ (((((2 * 16) - 1) * 8) + 8) <= 256)))]);
    b_x <-
    (BArray24.set64d b_x ((((2 * 16) - 1) %% 3) * 8)
    (W64.of_int 18446744073709551615));
    (aux_9, aux_10) <-
    (adc_64 (BArray24.get64 x (((2 * 16) - 1) %% 3))
    (BArray256.get64 a ((2 * 16) - 1)) false);
    cf <- aux_9;
    x <- (BArray24.set64 x (((2 * 16) - 1) %% 3) aux_10);
    ( _1, lastbit) <- (adc_64 lastbit (W64.of_int 0) cf);
    trace_h__H__MUL__UNR____mont_redM <-
    (trace_h__H__MUL__UNR____mont_redM ++
    [(Assert, ((0 <= ((16 - 1) * 8)) /\ ((((16 - 1) * 8) + 8) <= 128)))]);
    trace_h__H__MUL__UNR____mont_redM <-
    (trace_h__H__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= ((((2 * 16) - 1) %% 3) * 8)) /\
     ((((((2 * 16) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__H__MUL__UNR____mont_redM <-
    (trace_h__H__MUL__UNR____mont_redM ++
    [(Assert, (BArray24.is_init b_x ((((2 * 16) - 1) %% 3) * 8) 8))]);
    b_r <-
    (BArray128.set64d b_r ((16 - 1) * 8) (W64.of_int 18446744073709551615));
    r <-
    (BArray128.set64 r (16 - 1) (BArray24.get64 x (((2 * 16) - 1) %% 3)));
    trace_h__H__MUL__UNR____mont_redM <-
    (trace_h__H__MUL__UNR____mont_redM ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 256)))]);
    b_mP <- (SBArray256_128.get_sub64 b__P_mP 16);
    mP <- (SBArray256_128.get_sub64 _P_mP 16);
    b_param_5 <- b_r;
    param_23 <- r;
    b_param_6 <- b_mP;
    param_24 <- mP;
    param_25 <- lastbit;
    (aux_11, aux_12, tmp__trace) <@ h__H__BN___cminusP_ (param_23, b_param_5,
    param_24, b_param_6, param_25);
    result_4 <- aux_11;
    b_result_4 <- aux_12;
    trace_h__H__MUL__UNR____mont_redM <-
    (trace_h__H__MUL__UNR____mont_redM ++ tmp__trace);
    trace_h__H__MUL__UNR____mont_redM <-
    (trace_h__H__MUL__UNR____mont_redM ++
    [(Assert, (BArray128.is_init b_result_4 0 128))]);
    r <- result_4;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__UNR____mont_redM);
  }
  proc h__H__MUL__LOOP____mul1 (r:BArray256.t, b_r:BArray256.t, a:W64.t,
                                b:BArray128.t, b_b:BArray128.t) : BArray256.t *
                                                                  BArray256.t *
                                                                  trace = {
    var lo:W64.t;
    var hi:W64.t;
    var c:W64.t;
    var i:int;
    var cf:bool;
    var  _0:bool;
    var trace_h__H__MUL__LOOP____mul1:trace;
    trace_h__H__MUL__LOOP____mul1 <- [];
    trace_h__H__MUL__LOOP____mul1 <-
    (trace_h__H__MUL__LOOP____mul1 ++
    [(Assert, (BArray128.is_init b_b 0 128))]);
    lo <- (BArray128.get64 b 0);
    (hi, lo) <- (mulu_64 lo a);
    b_r <- (BArray256.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 0 lo);
    c <- hi;
    i <- 1;
    while ((i < 16)) {
      trace_h__H__MUL__LOOP____mul1 <-
      (trace_h__H__MUL__LOOP____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      lo <- (BArray128.get64 b i);
      (hi, lo) <- (mulu_64 lo a);
      (cf, lo) <- (adc_64 lo c false);
      ( _0, hi) <- (adc_64 hi (W64.of_int 0) cf);
      trace_h__H__MUL__LOOP____mul1 <-
      (trace_h__H__MUL__LOOP____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r i lo);
      c <- hi;
      i <- (i + 1);
    }
    trace_h__H__MUL__LOOP____mul1 <-
    (trace_h__H__MUL__LOOP____mul1 ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 8) <= 256)))]);
    b_r <- (BArray256.set64d b_r (16 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 16 c);
    return (r, b_r, trace_h__H__MUL__LOOP____mul1);
  }
  proc h__H__MUL__LOOP____mul1acc (k:W64.t, r:BArray256.t, b_r:BArray256.t,
                                   a:W64.t, b:BArray128.t, b_b:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var lo:W64.t;
    var hi:W64.t;
    var cf:bool;
    var c:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__H__MUL__LOOP____mul1acc:trace;
    trace_h__H__MUL__LOOP____mul1acc <- [];
    trace_h__H__MUL__LOOP____mul1acc <-
    (trace_h__H__MUL__LOOP____mul1acc ++
    [(Assert,
     ((((1 <= (W64.to_uint k)) /\ ((W64.to_uint k) < 16)) /\
      (BArray256.is_init b_r 0 (8 * ((W64.to_uint k) + 16)))) /\
     (BArray128.is_init b_b 0 128)))]);
    lo <- (BArray128.get64 b 0);
    (hi, lo) <- (mulu_64 lo a);
    trace_h__H__MUL__LOOP____mul1acc <-
    (trace_h__H__MUL__LOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__LOOP____mul1acc <-
    (trace_h__H__MUL__LOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__LOOP____mul1acc <-
    (trace_h__H__MUL__LOOP____mul1acc ++
    [(Assert, (BArray256.is_init b_r ((W64.to_uint k) * 8) 8))]);
    b_r <-
    (BArray256.set64d b_r ((W64.to_uint k) * 8)
    (W64.of_int 18446744073709551615));
    (aux, aux_0) <- (adc_64 (BArray256.get64 r (W64.to_uint k)) lo false);
    cf <- aux;
    r <- (BArray256.set64 r (W64.to_uint k) aux_0);
    ( _0, hi) <- (adc_64 hi (W64.of_int 0) cf);
    c <- hi;
    i <- 1;
    while ((i < 16)) {
      trace_h__H__MUL__LOOP____mul1acc <-
      (trace_h__H__MUL__LOOP____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      lo <- (BArray128.get64 b i);
      (hi, lo) <- (mulu_64 lo a);
      trace_h__H__MUL__LOOP____mul1acc <-
      (trace_h__H__MUL__LOOP____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__LOOP____mul1acc <-
      (trace_h__H__MUL__LOOP____mul1acc ++
      [(Assert,
       (BArray256.is_init b_r ((W64.to_uint (k + (W64.of_int i))) * 8) 8))]);
      (cf, lo) <-
      (adc_64 lo (BArray256.get64 r (W64.to_uint (k + (W64.of_int i)))) false
      );
      ( _1, hi) <- (adc_64 hi (W64.of_int 0) cf);
      (cf, lo) <- (adc_64 lo c false);
      ( _2, hi) <- (adc_64 hi (W64.of_int 0) cf);
      trace_h__H__MUL__LOOP____mul1acc <-
      (trace_h__H__MUL__LOOP____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r ((W64.to_uint (k + (W64.of_int i))) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r (W64.to_uint (k + (W64.of_int i))) lo);
      c <- hi;
      i <- (i + 1);
    }
    trace_h__H__MUL__LOOP____mul1acc <-
    (trace_h__H__MUL__LOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint (k + (W64.of_int 16))) * 8)) /\
     ((((W64.to_uint (k + (W64.of_int 16))) * 8) + 8) <= 256)))]);
    b_r <-
    (BArray256.set64d b_r ((W64.to_uint (k + (W64.of_int 16))) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r (W64.to_uint (k + (W64.of_int 16))) c);
    return (r, b_r, trace_h__H__MUL__LOOP____mul1acc);
  }
  proc h__H__MUL__LOOP___os_muln (r:BArray256.t, b_r:BArray256.t,
                                  a:BArray128.t, b_a:BArray128.t,
                                  b:BArray128.t, b_b:BArray128.t) : BArray256.t *
                                                                    BArray256.t *
                                                                    trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var ai:W64.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:W64.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray256.t;
    var param_3:BArray256.t;
    var param_4:W64.t;
    var param_5:BArray128.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var trace_h__H__MUL__LOOP___os_muln:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__H__MUL__LOOP___os_muln <- [];
    trace_h__H__MUL__LOOP___os_muln <-
    (trace_h__H__MUL__LOOP___os_muln ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    ai <- (BArray128.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__LOOP____mul1 (param, b_param,
    param_0, param_1, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__LOOP___os_muln <-
    (trace_h__H__MUL__LOOP___os_muln ++ tmp__trace);
    trace_h__H__MUL__LOOP___os_muln <-
    (trace_h__H__MUL__LOOP___os_muln ++
    [(Assert, (BArray256.is_init b_result 0 136))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 16))) {
      trace_h__H__MUL__LOOP___os_muln <-
      (trace_h__H__MUL__LOOP___os_muln ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 128)))]);
      ai <- (BArray128.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__H__MUL__LOOP____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray128.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__H__MUL__LOOP___os_muln <-
      (trace_h__H__MUL__LOOP___os_muln ++ tmp__trace);
      trace_h__H__MUL__LOOP___os_muln <-
      (trace_h__H__MUL__LOOP___os_muln ++
      [(Assert,
       (BArray256.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 16) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__H__MUL__LOOP___os_muln);
  }
  proc h__H__MUL__LOOP___os_muln_ (r:BArray256.t, b_r:BArray256.t,
                                   a:BArray128.t, b_a:BArray128.t,
                                   b:BArray128.t, b_b:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__MUL__LOOP___os_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__MUL__LOOP___os_muln_ <- [];
    trace_h__H__MUL__LOOP___os_muln_ <-
    (trace_h__H__MUL__LOOP___os_muln_ ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__LOOP___os_muln (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__LOOP___os_muln_ <-
    (trace_h__H__MUL__LOOP___os_muln_ ++ tmp__trace);
    trace_h__H__MUL__LOOP___os_muln_ <-
    (trace_h__H__MUL__LOOP___os_muln_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__LOOP___os_muln_);
  }
  proc h__H__MUL__LOOP___os_sqrn (r:BArray256.t, b_r:BArray256.t,
                                  a:BArray128.t, b_a:BArray128.t) : BArray256.t *
                                                                    BArray256.t *
                                                                    trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var ai:W64.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:W64.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray256.t;
    var param_3:BArray256.t;
    var param_4:W64.t;
    var param_5:BArray128.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var trace_h__H__MUL__LOOP___os_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__H__MUL__LOOP___os_sqrn <- [];
    trace_h__H__MUL__LOOP___os_sqrn <-
    (trace_h__H__MUL__LOOP___os_sqrn ++
    [(Assert, (BArray128.is_init b_a 0 128))]);
    ai <- (BArray128.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- a;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__LOOP____mul1 (param, b_param,
    param_0, param_1, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__LOOP___os_sqrn <-
    (trace_h__H__MUL__LOOP___os_sqrn ++ tmp__trace);
    trace_h__H__MUL__LOOP___os_sqrn <-
    (trace_h__H__MUL__LOOP___os_sqrn ++
    [(Assert, (BArray256.is_init b_result 0 136))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 16))) {
      trace_h__H__MUL__LOOP___os_sqrn <-
      (trace_h__H__MUL__LOOP___os_sqrn ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 128)))]);
      ai <- (BArray128.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- a;
      (aux_1, aux_2, tmp__trace) <@ h__H__MUL__LOOP____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray128.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__H__MUL__LOOP___os_sqrn <-
      (trace_h__H__MUL__LOOP___os_sqrn ++ tmp__trace);
      trace_h__H__MUL__LOOP___os_sqrn <-
      (trace_h__H__MUL__LOOP___os_sqrn ++
      [(Assert,
       (BArray256.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 16) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__H__MUL__LOOP___os_sqrn);
  }
  proc h__H__MUL__LOOP___os_sqrn_ (r:BArray256.t, b_r:BArray256.t,
                                   a:BArray128.t, b_a:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__MUL__LOOP___os_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__H__MUL__LOOP___os_sqrn_ <- [];
    trace_h__H__MUL__LOOP___os_sqrn_ <-
    (trace_h__H__MUL__LOOP___os_sqrn_ ++
    [(Assert, (BArray128.is_init b_a 0 128))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__LOOP___os_sqrn (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__LOOP___os_sqrn_ <-
    (trace_h__H__MUL__LOOP___os_sqrn_ ++ tmp__trace);
    trace_h__H__MUL__LOOP___os_sqrn_ <-
    (trace_h__H__MUL__LOOP___os_sqrn_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__LOOP___os_sqrn_);
  }
  proc h__H__MUL__LOOP____mont_redM (r:BArray128.t, b_r:BArray128.t,
                                     a:BArray256.t, b_a:BArray256.t,
                                     _P_mP:BArray256.t, b__P_mP:BArray256.t,
                                     _U0:W64.t) : BArray128.t * BArray128.t *
                                                  trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var i:int;
    var lo:W64.t;
    var c:W64.t;
    var k:W64.t;
    var m:W64.t;
    var hi:W64.t;
    var cf:bool;
    var w:W64.t;
    var b_mP:BArray128.t;
    var mP:BArray128.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var b_param_0:BArray128.t;
    var param_0:BArray128.t;
    var param_1:W64.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var trace_h__H__MUL__LOOP____mont_redM:trace;
    b_mP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    mP <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__H__MUL__LOOP____mont_redM <- [];
    trace_h__H__MUL__LOOP____mont_redM <-
    (trace_h__H__MUL__LOOP____mont_redM ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b__P_mP 0 256)))]);
    i <- 0;
    while ((i < 16)) {
      trace_h__H__MUL__LOOP____mont_redM <-
      (trace_h__H__MUL__LOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      lo <- (BArray256.get64 a i);
      trace_h__H__MUL__LOOP____mont_redM <-
      (trace_h__H__MUL__LOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      b_r <-
      (BArray128.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray128.set64 r i lo);
      i <- (i + 1);
    }
    c <- (W64.of_int 0);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 16))) {
      trace_h__H__MUL__LOOP____mont_redM <-
      (trace_h__H__MUL__LOOP____mont_redM ++
      [(Assert, (BArray128.is_init b_r 0 8))]);
      m <- (BArray128.get64 r 0);
      m <- (m * _U0);
      lo <- (BArray256.get64 _P_mP 0);
      (hi, lo) <- (mulu_64 lo m);
      trace_h__H__MUL__LOOP____mont_redM <-
      (trace_h__H__MUL__LOOP____mont_redM ++
      [(Assert, (BArray128.is_init b_r 0 8))]);
      (cf, lo) <- (adc_64 lo (BArray128.get64 r 0) false);
      ( _0, hi) <- (adc_64 hi (W64.of_int 0) cf);
      w <- hi;
      i <- 1;
      while ((i < 16)) {
        trace_h__H__MUL__LOOP____mont_redM <-
        (trace_h__H__MUL__LOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
        lo <- (BArray256.get64 _P_mP i);
        (hi, lo) <- (mulu_64 lo m);
        trace_h__H__MUL__LOOP____mont_redM <-
        (trace_h__H__MUL__LOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
        trace_h__H__MUL__LOOP____mont_redM <-
        (trace_h__H__MUL__LOOP____mont_redM ++
        [(Assert, (BArray128.is_init b_r (i * 8) 8))]);
        (cf, lo) <- (adc_64 lo (BArray128.get64 r i) false);
        ( _1, hi) <- (adc_64 hi (W64.of_int 0) cf);
        (cf, lo) <- (adc_64 lo w false);
        ( _2, hi) <- (adc_64 hi (W64.of_int 0) cf);
        trace_h__H__MUL__LOOP____mont_redM <-
        (trace_h__H__MUL__LOOP____mont_redM ++
        [(Assert, ((0 <= ((i - 1) * 8)) /\ ((((i - 1) * 8) + 8) <= 128)))]);
        b_r <-
        (BArray128.set64d b_r ((i - 1) * 8) (W64.of_int 18446744073709551615)
        );
        r <- (BArray128.set64 r (i - 1) lo);
        w <- hi;
        i <- (i + 1);
      }
      ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
      trace_h__H__MUL__LOOP____mont_redM <-
      (trace_h__H__MUL__LOOP____mont_redM ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int 16))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int 16))) * 8) + 8) <= 256)))]);
      (cf, w) <-
      (adc_64 w (BArray256.get64 a (W64.to_uint (k + (W64.of_int 16)))) cf);
      trace_h__H__MUL__LOOP____mont_redM <-
      (trace_h__H__MUL__LOOP____mont_redM ++
      [(Assert, ((0 <= ((16 - 1) * 8)) /\ ((((16 - 1) * 8) + 8) <= 128)))]);
      b_r <-
      (BArray128.set64d b_r ((16 - 1) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray128.set64 r (16 - 1) w);
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + (W64.of_int 1));
    }
    trace_h__H__MUL__LOOP____mont_redM <-
    (trace_h__H__MUL__LOOP____mont_redM ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 256)))]);
    b_mP <- (SBArray256_128.get_sub64 b__P_mP 16);
    mP <- (SBArray256_128.get_sub64 _P_mP 16);
    b_param <- b_r;
    param <- r;
    b_param_0 <- b_mP;
    param_0 <- mP;
    param_1 <- c;
    (aux, aux_0, tmp__trace) <@ h__H__BN___cminusP_ (param, b_param, 
    param_0, b_param_0, param_1);
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__LOOP____mont_redM <-
    (trace_h__H__MUL__LOOP____mont_redM ++ tmp__trace);
    trace_h__H__MUL__LOOP____mont_redM <-
    (trace_h__H__MUL__LOOP____mont_redM ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    r <- result;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__LOOP____mont_redM);
  }
  proc h__H__MUL__XUNR____mul1 (r:BArray256.t, b_r:BArray256.t, a:W64.t,
                                b:BArray128.t, b_b:BArray128.t) : BArray256.t *
                                                                  BArray256.t *
                                                                  trace = {
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var i:int;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__H__MUL__XUNR____mul1:trace;
    trace_h__H__MUL__XUNR____mul1 <- [];
    trace_h__H__MUL__XUNR____mul1 <-
    (trace_h__H__MUL__XUNR____mul1 ++
    [(Assert, (BArray128.is_init b_b 0 128))]);
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray128.get64 b 0));
    b_r <- (BArray256.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 0 lo);
    i <- 1;
    while ((i < 16)) {
      t <- hi;
      trace_h__H__MUL__XUNR____mul1 <-
      (trace_h__H__MUL__XUNR____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      (hi, lo) <- (MULX_64 a (BArray128.get64 b i));
      (cf, t) <- (ADCX_64 t lo cf);
      trace_h__H__MUL__XUNR____mul1 <-
      (trace_h__H__MUL__XUNR____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r i t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    trace_h__H__MUL__XUNR____mul1 <-
    (trace_h__H__MUL__XUNR____mul1 ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 8) <= 256)))]);
    b_r <- (BArray256.set64d b_r (16 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 16 hi);
    return (r, b_r, trace_h__H__MUL__XUNR____mul1);
  }
  proc h__H__MUL__XUNR____mul1acc (k:int, r:BArray256.t, b_r:BArray256.t,
                                   a:W64.t, b:BArray128.t, b_b:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var t:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__H__MUL__XUNR____mul1acc:trace;
    trace_h__H__MUL__XUNR____mul1acc <- [];
    trace_h__H__MUL__XUNR____mul1acc <-
    (trace_h__H__MUL__XUNR____mul1acc ++
    [(Assert,
     ((((1 <= k) /\ (k < 16)) /\ (BArray256.is_init b_r 0 (8 * (k + 16)))) /\
     (BArray128.is_init b_b 0 128)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray128.get64 b 0));
    trace_h__H__MUL__XUNR____mul1acc <-
    (trace_h__H__MUL__XUNR____mul1acc ++
    [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XUNR____mul1acc <-
    (trace_h__H__MUL__XUNR____mul1acc ++
    [(Assert, (BArray256.is_init b_r (k * 8) 8))]);
    t <- (BArray256.get64 r k);
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__H__MUL__XUNR____mul1acc <-
    (trace_h__H__MUL__XUNR____mul1acc ++
    [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
    b_r <- (BArray256.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r k t);
    i <- 1;
    while ((i < 16)) {
      trace_h__H__MUL__XUNR____mul1acc <-
      (trace_h__H__MUL__XUNR____mul1acc ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XUNR____mul1acc <-
      (trace_h__H__MUL__XUNR____mul1acc ++
      [(Assert, (BArray256.is_init b_r ((k + i) * 8) 8))]);
      t <- (BArray256.get64 r (k + i));
      (cf, t) <- (ADCX_64 t hi cf);
      trace_h__H__MUL__XUNR____mul1acc <-
      (trace_h__H__MUL__XUNR____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      (hi, lo) <- (MULX_64 a (BArray128.get64 b i));
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__H__MUL__XUNR____mul1acc <-
      (trace_h__H__MUL__XUNR____mul1acc ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r ((k + i) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r (k + i) t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__H__MUL__XUNR____mul1acc <-
    (trace_h__H__MUL__XUNR____mul1acc ++
    [(Assert, ((0 <= ((k + 16) * 8)) /\ ((((k + 16) * 8) + 8) <= 256)))]);
    b_r <-
    (BArray256.set64d b_r ((k + 16) * 8) (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r (k + 16) hi);
    return (r, b_r, trace_h__H__MUL__XUNR____mul1acc);
  }
  proc h__H__MUL__XUNR___os_muln (r:BArray256.t, b_r:BArray256.t,
                                  a:BArray128.t, b_a:BArray128.t,
                                  b:BArray128.t, b_b:BArray128.t) : BArray256.t *
                                                                    BArray256.t *
                                                                    trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var ai:W64.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:W64.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var k:int;
    var param_2:int;
    var b_param_0:BArray256.t;
    var param_3:BArray256.t;
    var param_4:W64.t;
    var param_5:BArray128.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var trace_h__H__MUL__XUNR___os_muln:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__H__MUL__XUNR___os_muln <- [];
    trace_h__H__MUL__XUNR___os_muln <-
    (trace_h__H__MUL__XUNR___os_muln ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    ai <- (BArray128.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__XUNR____mul1 (param, b_param,
    param_0, param_1, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__XUNR___os_muln <-
    (trace_h__H__MUL__XUNR___os_muln ++ tmp__trace);
    trace_h__H__MUL__XUNR___os_muln <-
    (trace_h__H__MUL__XUNR___os_muln ++
    [(Assert, (BArray256.is_init b_result 0 136))]);
    b_r <- b_result;
    r <- result;
    k <- 1;
    while ((k < 16)) {
      trace_h__H__MUL__XUNR___os_muln <-
      (trace_h__H__MUL__XUNR___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 128)))]);
      ai <- (BArray128.get64 a k);
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__H__MUL__XUNR____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray128.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__H__MUL__XUNR___os_muln <-
      (trace_h__H__MUL__XUNR___os_muln ++ tmp__trace);
      trace_h__H__MUL__XUNR___os_muln <-
      (trace_h__H__MUL__XUNR___os_muln ++
      [(Assert, (BArray256.is_init b_result_0 0 (8 * ((param_2 + 16) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + 1);
    }
    return (r, b_r, trace_h__H__MUL__XUNR___os_muln);
  }
  proc h__H__MUL__XUNR___os_muln_ (r:BArray256.t, b_r:BArray256.t,
                                   a:BArray128.t, b_a:BArray128.t,
                                   b:BArray128.t, b_b:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__MUL__XUNR___os_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__MUL__XUNR___os_muln_ <- [];
    trace_h__H__MUL__XUNR___os_muln_ <-
    (trace_h__H__MUL__XUNR___os_muln_ ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__XUNR___os_muln (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__XUNR___os_muln_ <-
    (trace_h__H__MUL__XUNR___os_muln_ ++ tmp__trace);
    trace_h__H__MUL__XUNR___os_muln_ <-
    (trace_h__H__MUL__XUNR___os_muln_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__XUNR___os_muln_);
  }
  proc h__H__MUL__XUNR____sqr_row0 (r:BArray256.t, b_r:BArray256.t,
                                    a:BArray128.t, b_a:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var j:int;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__H__MUL__XUNR____sqr_row0:trace;
    trace_h__H__MUL__XUNR____sqr_row0 <- [];
    trace_h__H__MUL__XUNR____sqr_row0 <-
    (trace_h__H__MUL__XUNR____sqr_row0 ++
    [(Assert, ((2 <= 16) /\ (BArray128.is_init b_a 0 128)))]);
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    ai <- (BArray128.get64 a 0);
    (hi, lo) <- (MULX_64 ai (BArray128.get64 a 1));
    b_r <- (BArray256.set64d b_r 8 (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 1 lo);
    j <- 2;
    while ((j < 16)) {
      t <- hi;
      trace_h__H__MUL__XUNR____sqr_row0 <-
      (trace_h__H__MUL__XUNR____sqr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 128)))]);
      (hi, lo) <- (MULX_64 ai (BArray128.get64 a j));
      (cf, t) <- (ADCX_64 t lo cf);
      trace_h__H__MUL__XUNR____sqr_row0 <-
      (trace_h__H__MUL__XUNR____sqr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (j * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r j t);
      j <- (j + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    trace_h__H__MUL__XUNR____sqr_row0 <-
    (trace_h__H__MUL__XUNR____sqr_row0 ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 8) <= 256)))]);
    b_r <- (BArray256.set64d b_r (16 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 16 hi);
    return (r, b_r, trace_h__H__MUL__XUNR____sqr_row0);
  }
  proc h__H__MUL__XUNR____sqr_rowacc (i:int, r:BArray256.t, b_r:BArray256.t,
                                      a:BArray128.t, b_a:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var t:W64.t;
    var j:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__H__MUL__XUNR____sqr_rowacc:trace;
    trace_h__H__MUL__XUNR____sqr_rowacc <- [];
    trace_h__H__MUL__XUNR____sqr_rowacc <-
    (trace_h__H__MUL__XUNR____sqr_rowacc ++
    [(Assert,
     ((((1 <= i) /\ (i < (16 - 1))) /\
      (BArray256.is_init b_r 8 (8 * ((i + 16) - 1)))) /\
     (BArray128.is_init b_a 0 128)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    trace_h__H__MUL__XUNR____sqr_rowacc <-
    (trace_h__H__MUL__XUNR____sqr_rowacc ++
    [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
    ai <- (BArray128.get64 a i);
    trace_h__H__MUL__XUNR____sqr_rowacc <-
    (trace_h__H__MUL__XUNR____sqr_rowacc ++
    [(Assert, ((0 <= ((i + 1) * 8)) /\ ((((i + 1) * 8) + 8) <= 128)))]);
    (hi, lo) <- (MULX_64 ai (BArray128.get64 a (i + 1)));
    trace_h__H__MUL__XUNR____sqr_rowacc <-
    (trace_h__H__MUL__XUNR____sqr_rowacc ++
    [(Assert,
     ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XUNR____sqr_rowacc <-
    (trace_h__H__MUL__XUNR____sqr_rowacc ++
    [(Assert, (BArray256.is_init b_r (((2 * i) + 1) * 8) 8))]);
    t <- (BArray256.get64 r ((2 * i) + 1));
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__H__MUL__XUNR____sqr_rowacc <-
    (trace_h__H__MUL__XUNR____sqr_rowacc ++
    [(Assert,
     ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 256)))]);
    b_r <-
    (BArray256.set64d b_r (((2 * i) + 1) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r ((2 * i) + 1) t);
    j <- (i + 2);
    while ((j < 16)) {
      trace_h__H__MUL__XUNR____sqr_rowacc <-
      (trace_h__H__MUL__XUNR____sqr_rowacc ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XUNR____sqr_rowacc <-
      (trace_h__H__MUL__XUNR____sqr_rowacc ++
      [(Assert, (BArray256.is_init b_r ((i + j) * 8) 8))]);
      t <- (BArray256.get64 r (i + j));
      (cf, t) <- (ADCX_64 t hi cf);
      trace_h__H__MUL__XUNR____sqr_rowacc <-
      (trace_h__H__MUL__XUNR____sqr_rowacc ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 128)))]);
      (hi, lo) <- (MULX_64 ai (BArray128.get64 a j));
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__H__MUL__XUNR____sqr_rowacc <-
      (trace_h__H__MUL__XUNR____sqr_rowacc ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r ((i + j) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r (i + j) t);
      j <- (j + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__H__MUL__XUNR____sqr_rowacc <-
    (trace_h__H__MUL__XUNR____sqr_rowacc ++
    [(Assert, ((0 <= ((i + 16) * 8)) /\ ((((i + 16) * 8) + 8) <= 256)))]);
    b_r <-
    (BArray256.set64d b_r ((i + 16) * 8) (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r (i + 16) hi);
    return (r, b_r, trace_h__H__MUL__XUNR____sqr_rowacc);
  }
  proc h__H__MUL__XUNR____sqr_diag (r:BArray256.t, b_r:BArray256.t,
                                    a:BArray128.t, b_a:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var inc:int;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var t:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__H__MUL__XUNR____sqr_diag:trace;
    trace_h__H__MUL__XUNR____sqr_diag <- [];
    trace_h__H__MUL__XUNR____sqr_diag <-
    (trace_h__H__MUL__XUNR____sqr_diag ++
    [(Assert,
     (((2 <= 16) /\ (BArray256.is_init b_r 8 240)) /\
     (BArray128.is_init b_a 0 128)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    ai <- (BArray128.get64 a 0);
    (hi, lo) <- (MULX_64 ai (BArray128.get64 a 0));
    b_r <- (BArray256.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 0 lo);
    trace_h__H__MUL__XUNR____sqr_diag <-
    (trace_h__H__MUL__XUNR____sqr_diag ++
    [(Assert, (BArray256.is_init b_r 8 8))]);
    t <- (BArray256.get64 r 1);
    (cf, t) <- (ADCX_64 t t cf);
    (of_0, t) <- (ADOX_64 t hi of_0);
    b_r <- (BArray256.set64d b_r 8 (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 1 t);
    inc <- (16 - 1);
    i <- 1;
    while ((i < inc)) {
      trace_h__H__MUL__XUNR____sqr_diag <-
      (trace_h__H__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      ai <- (BArray128.get64 a i);
      trace_h__H__MUL__XUNR____sqr_diag <-
      (trace_h__H__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      (hi, lo) <- (MULX_64 ai (BArray128.get64 a i));
      trace_h__H__MUL__XUNR____sqr_diag <-
      (trace_h__H__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= ((2 * i) * 8)) /\ ((((2 * i) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XUNR____sqr_diag <-
      (trace_h__H__MUL__XUNR____sqr_diag ++
      [(Assert, (BArray256.is_init b_r ((2 * i) * 8) 8))]);
      t <- (BArray256.get64 r (2 * i));
      (cf, t) <- (ADCX_64 t t cf);
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__H__MUL__XUNR____sqr_diag <-
      (trace_h__H__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= ((2 * i) * 8)) /\ ((((2 * i) * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r ((2 * i) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r (2 * i) t);
      trace_h__H__MUL__XUNR____sqr_diag <-
      (trace_h__H__MUL__XUNR____sqr_diag ++
      [(Assert,
       ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XUNR____sqr_diag <-
      (trace_h__H__MUL__XUNR____sqr_diag ++
      [(Assert, (BArray256.is_init b_r (((2 * i) + 1) * 8) 8))]);
      t <- (BArray256.get64 r ((2 * i) + 1));
      (cf, t) <- (ADCX_64 t t cf);
      (of_0, t) <- (ADOX_64 t hi of_0);
      trace_h__H__MUL__XUNR____sqr_diag <-
      (trace_h__H__MUL__XUNR____sqr_diag ++
      [(Assert,
       ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (((2 * i) + 1) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r ((2 * i) + 1) t);
      i <- (i + 1);
    }
    trace_h__H__MUL__XUNR____sqr_diag <-
    (trace_h__H__MUL__XUNR____sqr_diag ++
    [(Assert, ((0 <= ((16 - 1) * 8)) /\ ((((16 - 1) * 8) + 8) <= 128)))]);
    ai <- (BArray128.get64 a (16 - 1));
    trace_h__H__MUL__XUNR____sqr_diag <-
    (trace_h__H__MUL__XUNR____sqr_diag ++
    [(Assert, ((0 <= ((16 - 1) * 8)) /\ ((((16 - 1) * 8) + 8) <= 128)))]);
    (hi, lo) <- (MULX_64 ai (BArray128.get64 a (16 - 1)));
    trace_h__H__MUL__XUNR____sqr_diag <-
    (trace_h__H__MUL__XUNR____sqr_diag ++
    [(Assert,
     ((0 <= (((2 * 16) - 2) * 8)) /\ (((((2 * 16) - 2) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XUNR____sqr_diag <-
    (trace_h__H__MUL__XUNR____sqr_diag ++
    [(Assert, (BArray256.is_init b_r (((2 * 16) - 2) * 8) 8))]);
    t <- (BArray256.get64 r ((2 * 16) - 2));
    (cf, t) <- (ADCX_64 t t cf);
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__H__MUL__XUNR____sqr_diag <-
    (trace_h__H__MUL__XUNR____sqr_diag ++
    [(Assert,
     ((0 <= (((2 * 16) - 2) * 8)) /\ (((((2 * 16) - 2) * 8) + 8) <= 256)))]);
    b_r <-
    (BArray256.set64d b_r (((2 * 16) - 2) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r ((2 * 16) - 2) t);
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__H__MUL__XUNR____sqr_diag <-
    (trace_h__H__MUL__XUNR____sqr_diag ++
    [(Assert,
     ((0 <= (((2 * 16) - 1) * 8)) /\ (((((2 * 16) - 1) * 8) + 8) <= 256)))]);
    b_r <-
    (BArray256.set64d b_r (((2 * 16) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r ((2 * 16) - 1) hi);
    return (r, b_r, trace_h__H__MUL__XUNR____sqr_diag);
  }
  proc h__H__MUL__XUNR___os_sqrn (r:BArray256.t, b_r:BArray256.t,
                                  a:BArray128.t, b_a:BArray128.t) : BArray256.t *
                                                                    BArray256.t *
                                                                    trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var aux_3:BArray256.t;
    var aux_4:BArray256.t;
    var inc:int;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var i:int;
    var param_1:int;
    var b_param_0:BArray256.t;
    var param_2:BArray256.t;
    var param_3:BArray128.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var b_param_1:BArray256.t;
    var param_4:BArray256.t;
    var param_5:BArray128.t;
    var result_1:BArray256.t;
    var b_result_1:BArray256.t;
    var trace_h__H__MUL__XUNR___os_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    param <- witness;
    param_0 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_h__H__MUL__XUNR___os_sqrn <- [];
    trace_h__H__MUL__XUNR___os_sqrn <-
    (trace_h__H__MUL__XUNR___os_sqrn ++
    [(Assert, (BArray128.is_init b_a 0 128))]);
    if ((16 = 1)) {
      trace_h__H__MUL__XUNR___os_sqrn <-
      (trace_h__H__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 128)))]);
      ai <- (BArray128.get64 a 0);
      trace_h__H__MUL__XUNR___os_sqrn <-
      (trace_h__H__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 128)))]);
      (hi, lo) <- (MULX_64 ai (BArray128.get64 a 0));
      trace_h__H__MUL__XUNR___os_sqrn <-
      (trace_h__H__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (0 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r 0 lo);
      trace_h__H__MUL__XUNR___os_sqrn <-
      (trace_h__H__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (1 * 8)) /\ (((1 * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (1 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r 1 hi);
    } else {
      b_param <- b_r;
      param <- r;
      param_0 <- a;
      (aux, aux_0, tmp__trace) <@ h__H__MUL__XUNR____sqr_row0 (param,
      b_param, param_0, (BArray128.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__H__MUL__XUNR___os_sqrn <-
      (trace_h__H__MUL__XUNR___os_sqrn ++ tmp__trace);
      trace_h__H__MUL__XUNR___os_sqrn <-
      (trace_h__H__MUL__XUNR___os_sqrn ++
      [(Assert, (BArray256.is_init b_result 8 128))]);
      b_r <- b_result;
      r <- result;
      inc <- (16 - 1);
      i <- 1;
      while ((i < inc)) {
        param_1 <- i;
        b_param_0 <- b_r;
        param_2 <- r;
        param_3 <- a;
        (aux_1, aux_2, tmp__trace) <@ h__H__MUL__XUNR____sqr_rowacc (
        param_1, param_2, b_param_0, param_3,
        (BArray128.init_arr (W8.of_int 255)));
        result_0 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__H__MUL__XUNR___os_sqrn <-
        (trace_h__H__MUL__XUNR___os_sqrn ++ tmp__trace);
        trace_h__H__MUL__XUNR___os_sqrn <-
        (trace_h__H__MUL__XUNR___os_sqrn ++
        [(Assert, (BArray256.is_init b_result_0 8 (8 * (param_1 + 16))))]);
        b_r <- b_result_0;
        r <- result_0;
        i <- (i + 1);
      }
      b_param_1 <- b_r;
      param_4 <- r;
      param_5 <- a;
      (aux_3, aux_4, tmp__trace) <@ h__H__MUL__XUNR____sqr_diag (param_4,
      b_param_1, param_5, (BArray128.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__H__MUL__XUNR___os_sqrn <-
      (trace_h__H__MUL__XUNR___os_sqrn ++ tmp__trace);
      trace_h__H__MUL__XUNR___os_sqrn <-
      (trace_h__H__MUL__XUNR___os_sqrn ++
      [(Assert, (BArray256.is_init b_result_1 0 256))]);
      b_r <- (BArray256.init_arr (W8.of_int 255));
      r <- result_1;
    }
    return (r, b_r, trace_h__H__MUL__XUNR___os_sqrn);
  }
  proc h__H__MUL__XUNR___os_sqrn_ (r:BArray256.t, b_r:BArray256.t,
                                   a:BArray128.t, b_a:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__MUL__XUNR___os_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__H__MUL__XUNR___os_sqrn_ <- [];
    trace_h__H__MUL__XUNR___os_sqrn_ <-
    (trace_h__H__MUL__XUNR___os_sqrn_ ++
    [(Assert, (BArray128.is_init b_a 0 128))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__XUNR___os_sqrn (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__XUNR___os_sqrn_ <-
    (trace_h__H__MUL__XUNR___os_sqrn_ ++ tmp__trace);
    trace_h__H__MUL__XUNR___os_sqrn_ <-
    (trace_h__H__MUL__XUNR___os_sqrn_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__XUNR___os_sqrn_);
  }
  proc h__H__MUL__XUNR____mont_redM (r:BArray128.t, b_r:BArray128.t,
                                     a:BArray256.t, b_a:BArray256.t,
                                     _P_mP:BArray256.t, b__P_mP:BArray256.t,
                                     _U0:W64.t) : BArray128.t * BArray128.t *
                                                  trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var c:W64.t;
    var w0:W64.t;
    var k:int;
    var m:W64.t;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var i:int;
    var t:W64.t;
    var b_mP:BArray128.t;
    var mP:BArray128.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var b_param_0:BArray128.t;
    var param_0:BArray128.t;
    var param_1:W64.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var trace_h__H__MUL__XUNR____mont_redM:trace;
    b_mP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    mP <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__H__MUL__XUNR____mont_redM <- [];
    trace_h__H__MUL__XUNR____mont_redM <-
    (trace_h__H__MUL__XUNR____mont_redM ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b__P_mP 0 256)))]);
    c <- (W64.of_int 0);
    w0 <- (BArray256.get64 a 0);
    k <- 0;
    while ((k < 16)) {
      m <- w0;
      m <- (m * _U0);
      (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
      (hi, lo) <- (MULX_64 m (BArray256.get64 _P_mP 0));
      (of_0, w0) <- (ADOX_64 w0 lo of_0);
      i <- 1;
      while ((i < 16)) {
        if ((k = 0)) {
          trace_h__H__MUL__XUNR____mont_redM <-
          (trace_h__H__MUL__XUNR____mont_redM ++
          [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
          t <- (BArray256.get64 a i);
        } else {
          trace_h__H__MUL__XUNR____mont_redM <-
          (trace_h__H__MUL__XUNR____mont_redM ++
          [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
          trace_h__H__MUL__XUNR____mont_redM <-
          (trace_h__H__MUL__XUNR____mont_redM ++
          [(Assert, (BArray128.is_init b_r (i * 8) 8))]);
          t <- (BArray128.get64 r i);
        }
        (cf, t) <- (ADCX_64 t hi cf);
        trace_h__H__MUL__XUNR____mont_redM <-
        (trace_h__H__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
        (hi, lo) <- (MULX_64 m (BArray256.get64 _P_mP i));
        (of_0, t) <- (ADOX_64 t lo of_0);
        trace_h__H__MUL__XUNR____mont_redM <-
        (trace_h__H__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= ((i - 1) * 8)) /\ ((((i - 1) * 8) + 8) <= 128)))]);
        b_r <-
        (BArray128.set64d b_r ((i - 1) * 8) (W64.of_int 18446744073709551615)
        );
        r <- (BArray128.set64 r (i - 1) t);
        if ((i = 1)) {
          w0 <- t;
        } else {
          
        }
        i <- (i + 1);
      }
      (cf, hi) <- (ADCX_64 hi _zero cf);
      (of_0, hi) <- (ADOX_64 hi _zero of_0);
      if ((k = 0)) {
        trace_h__H__MUL__XUNR____mont_redM <-
        (trace_h__H__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 8) <= 256)))]);
        (cf, hi) <- (adc_64 hi (BArray256.get64 a 16) false);
      } else {
        ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
        trace_h__H__MUL__XUNR____mont_redM <-
        (trace_h__H__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= ((k + 16) * 8)) /\ ((((k + 16) * 8) + 8) <= 256)))]);
        (cf, hi) <- (adc_64 hi (BArray256.get64 a (k + 16)) cf);
      }
      trace_h__H__MUL__XUNR____mont_redM <-
      (trace_h__H__MUL__XUNR____mont_redM ++
      [(Assert, ((0 <= ((16 - 1) * 8)) /\ ((((16 - 1) * 8) + 8) <= 128)))]);
      b_r <-
      (BArray128.set64d b_r ((16 - 1) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray128.set64 r (16 - 1) hi);
      if ((16 = 1)) {
        w0 <- hi;
      } else {
        
      }
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + 1);
    }
    trace_h__H__MUL__XUNR____mont_redM <-
    (trace_h__H__MUL__XUNR____mont_redM ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 256)))]);
    b_mP <- (SBArray256_128.get_sub64 b__P_mP 16);
    mP <- (SBArray256_128.get_sub64 _P_mP 16);
    b_param <- b_r;
    param <- r;
    b_param_0 <- b_mP;
    param_0 <- mP;
    param_1 <- c;
    (aux, aux_0, tmp__trace) <@ h__H__BN___cminusP_ (param, b_param, 
    param_0, b_param_0, param_1);
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__XUNR____mont_redM <-
    (trace_h__H__MUL__XUNR____mont_redM ++ tmp__trace);
    trace_h__H__MUL__XUNR____mont_redM <-
    (trace_h__H__MUL__XUNR____mont_redM ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    r <- result;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__XUNR____mont_redM);
  }
  proc h__H__MUL__XLOOP____mul1 (r:BArray256.t, b_r:BArray256.t, a:W64.t,
                                 b:BArray128.t, b_b:BArray128.t) : BArray256.t *
                                                                   BArray256.t *
                                                                   trace = {
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var i:int;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__H__MUL__XLOOP____mul1:trace;
    trace_h__H__MUL__XLOOP____mul1 <- [];
    trace_h__H__MUL__XLOOP____mul1 <-
    (trace_h__H__MUL__XLOOP____mul1 ++
    [(Assert, (BArray128.is_init b_b 0 128))]);
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray128.get64 b 0));
    b_r <- (BArray256.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 0 lo);
    i <- 1;
    while ((i < 16)) {
      t <- hi;
      trace_h__H__MUL__XLOOP____mul1 <-
      (trace_h__H__MUL__XLOOP____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      (hi, lo) <- (MULX_64 a (BArray128.get64 b i));
      (cf, t) <- (ADCX_64 t lo cf);
      trace_h__H__MUL__XLOOP____mul1 <-
      (trace_h__H__MUL__XLOOP____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r i t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    trace_h__H__MUL__XLOOP____mul1 <-
    (trace_h__H__MUL__XLOOP____mul1 ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 8) <= 256)))]);
    b_r <- (BArray256.set64d b_r (16 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 16 hi);
    return (r, b_r, trace_h__H__MUL__XLOOP____mul1);
  }
  proc h__H__MUL__XLOOP____mul1acc (k:W64.t, r:BArray256.t, b_r:BArray256.t,
                                    a:W64.t, b:BArray128.t, b_b:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var t:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__H__MUL__XLOOP____mul1acc:trace;
    trace_h__H__MUL__XLOOP____mul1acc <- [];
    trace_h__H__MUL__XLOOP____mul1acc <-
    (trace_h__H__MUL__XLOOP____mul1acc ++
    [(Assert,
     ((((1 <= (W64.to_uint k)) /\ ((W64.to_uint k) < 16)) /\
      (BArray256.is_init b_r 0 (8 * ((W64.to_uint k) + 16)))) /\
     (BArray128.is_init b_b 0 128)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray128.get64 b 0));
    trace_h__H__MUL__XLOOP____mul1acc <-
    (trace_h__H__MUL__XLOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XLOOP____mul1acc <-
    (trace_h__H__MUL__XLOOP____mul1acc ++
    [(Assert, (BArray256.is_init b_r ((W64.to_uint k) * 8) 8))]);
    t <- (BArray256.get64 r (W64.to_uint k));
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__H__MUL__XLOOP____mul1acc <-
    (trace_h__H__MUL__XLOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 256)))]);
    b_r <-
    (BArray256.set64d b_r ((W64.to_uint k) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r (W64.to_uint k) t);
    i <- 1;
    while ((i < 16)) {
      trace_h__H__MUL__XLOOP____mul1acc <-
      (trace_h__H__MUL__XLOOP____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XLOOP____mul1acc <-
      (trace_h__H__MUL__XLOOP____mul1acc ++
      [(Assert,
       (BArray256.is_init b_r ((W64.to_uint (k + (W64.of_int i))) * 8) 8))]);
      t <- (BArray256.get64 r (W64.to_uint (k + (W64.of_int i))));
      (cf, t) <- (ADCX_64 t hi cf);
      trace_h__H__MUL__XLOOP____mul1acc <-
      (trace_h__H__MUL__XLOOP____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      (hi, lo) <- (MULX_64 a (BArray128.get64 b i));
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__H__MUL__XLOOP____mul1acc <-
      (trace_h__H__MUL__XLOOP____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r ((W64.to_uint (k + (W64.of_int i))) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r (W64.to_uint (k + (W64.of_int i))) t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__H__MUL__XLOOP____mul1acc <-
    (trace_h__H__MUL__XLOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint (k + (W64.of_int 16))) * 8)) /\
     ((((W64.to_uint (k + (W64.of_int 16))) * 8) + 8) <= 256)))]);
    b_r <-
    (BArray256.set64d b_r ((W64.to_uint (k + (W64.of_int 16))) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r (W64.to_uint (k + (W64.of_int 16))) hi);
    return (r, b_r, trace_h__H__MUL__XLOOP____mul1acc);
  }
  proc h__H__MUL__XLOOP___os_muln (r:BArray256.t, b_r:BArray256.t,
                                   a:BArray128.t, b_a:BArray128.t,
                                   b:BArray128.t, b_b:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var ai:W64.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:W64.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray256.t;
    var param_3:BArray256.t;
    var param_4:W64.t;
    var param_5:BArray128.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var trace_h__H__MUL__XLOOP___os_muln:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__H__MUL__XLOOP___os_muln <- [];
    trace_h__H__MUL__XLOOP___os_muln <-
    (trace_h__H__MUL__XLOOP___os_muln ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    ai <- (BArray128.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__XLOOP____mul1 (param, b_param,
    param_0, param_1, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__XLOOP___os_muln <-
    (trace_h__H__MUL__XLOOP___os_muln ++ tmp__trace);
    trace_h__H__MUL__XLOOP___os_muln <-
    (trace_h__H__MUL__XLOOP___os_muln ++
    [(Assert, (BArray256.is_init b_result 0 136))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 16))) {
      trace_h__H__MUL__XLOOP___os_muln <-
      (trace_h__H__MUL__XLOOP___os_muln ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 128)))]);
      ai <- (BArray128.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__H__MUL__XLOOP____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray128.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__H__MUL__XLOOP___os_muln <-
      (trace_h__H__MUL__XLOOP___os_muln ++ tmp__trace);
      trace_h__H__MUL__XLOOP___os_muln <-
      (trace_h__H__MUL__XLOOP___os_muln ++
      [(Assert,
       (BArray256.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 16) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__H__MUL__XLOOP___os_muln);
  }
  proc h__H__MUL__XLOOP___os_muln_ (r:BArray256.t, b_r:BArray256.t,
                                    a:BArray128.t, b_a:BArray128.t,
                                    b:BArray128.t, b_b:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__MUL__XLOOP___os_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__MUL__XLOOP___os_muln_ <- [];
    trace_h__H__MUL__XLOOP___os_muln_ <-
    (trace_h__H__MUL__XLOOP___os_muln_ ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__XLOOP___os_muln (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__XLOOP___os_muln_ <-
    (trace_h__H__MUL__XLOOP___os_muln_ ++ tmp__trace);
    trace_h__H__MUL__XLOOP___os_muln_ <-
    (trace_h__H__MUL__XLOOP___os_muln_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__XLOOP___os_muln_);
  }
  proc h__H__MUL__XLOOP___os_sqrn (r:BArray256.t, b_r:BArray256.t,
                                   a:BArray128.t, b_a:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var ai:W64.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:W64.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray256.t;
    var param_3:BArray256.t;
    var param_4:W64.t;
    var param_5:BArray128.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var trace_h__H__MUL__XLOOP___os_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__H__MUL__XLOOP___os_sqrn <- [];
    trace_h__H__MUL__XLOOP___os_sqrn <-
    (trace_h__H__MUL__XLOOP___os_sqrn ++
    [(Assert, (BArray128.is_init b_a 0 128))]);
    ai <- (BArray128.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- a;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__XLOOP____mul1 (param, b_param,
    param_0, param_1, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__XLOOP___os_sqrn <-
    (trace_h__H__MUL__XLOOP___os_sqrn ++ tmp__trace);
    trace_h__H__MUL__XLOOP___os_sqrn <-
    (trace_h__H__MUL__XLOOP___os_sqrn ++
    [(Assert, (BArray256.is_init b_result 0 136))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 16))) {
      trace_h__H__MUL__XLOOP___os_sqrn <-
      (trace_h__H__MUL__XLOOP___os_sqrn ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 128)))]);
      ai <- (BArray128.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- a;
      (aux_1, aux_2, tmp__trace) <@ h__H__MUL__XLOOP____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray128.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__H__MUL__XLOOP___os_sqrn <-
      (trace_h__H__MUL__XLOOP___os_sqrn ++ tmp__trace);
      trace_h__H__MUL__XLOOP___os_sqrn <-
      (trace_h__H__MUL__XLOOP___os_sqrn ++
      [(Assert,
       (BArray256.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 16) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__H__MUL__XLOOP___os_sqrn);
  }
  proc h__H__MUL__XLOOP___os_sqrn_ (r:BArray256.t, b_r:BArray256.t,
                                    a:BArray128.t, b_a:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__MUL__XLOOP___os_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__H__MUL__XLOOP___os_sqrn_ <- [];
    trace_h__H__MUL__XLOOP___os_sqrn_ <-
    (trace_h__H__MUL__XLOOP___os_sqrn_ ++
    [(Assert, (BArray128.is_init b_a 0 128))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__XLOOP___os_sqrn (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__XLOOP___os_sqrn_ <-
    (trace_h__H__MUL__XLOOP___os_sqrn_ ++ tmp__trace);
    trace_h__H__MUL__XLOOP___os_sqrn_ <-
    (trace_h__H__MUL__XLOOP___os_sqrn_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__XLOOP___os_sqrn_);
  }
  proc h__H__MUL__XLOOP____mont_redM (r:BArray128.t, b_r:BArray128.t,
                                      a:BArray256.t, b_a:BArray256.t,
                                      _P_mP:BArray256.t, b__P_mP:BArray256.t,
                                      _U0:W64.t) : BArray128.t *
                                                   BArray128.t * trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var i:int;
    var t:W64.t;
    var c:W64.t;
    var k:W64.t;
    var m:W64.t;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var b_mP:BArray128.t;
    var mP:BArray128.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var b_param_0:BArray128.t;
    var param_0:BArray128.t;
    var param_1:W64.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var trace_h__H__MUL__XLOOP____mont_redM:trace;
    b_mP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    mP <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__H__MUL__XLOOP____mont_redM <- [];
    trace_h__H__MUL__XLOOP____mont_redM <-
    (trace_h__H__MUL__XLOOP____mont_redM ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b__P_mP 0 256)))]);
    i <- 0;
    while ((i < 16)) {
      trace_h__H__MUL__XLOOP____mont_redM <-
      (trace_h__H__MUL__XLOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      t <- (BArray256.get64 a i);
      trace_h__H__MUL__XLOOP____mont_redM <-
      (trace_h__H__MUL__XLOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      b_r <-
      (BArray128.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray128.set64 r i t);
      i <- (i + 1);
    }
    c <- (W64.of_int 0);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 16))) {
      trace_h__H__MUL__XLOOP____mont_redM <-
      (trace_h__H__MUL__XLOOP____mont_redM ++
      [(Assert, (BArray128.is_init b_r 0 8))]);
      m <- (BArray128.get64 r 0);
      m <- (m * _U0);
      (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
      (hi, lo) <- (MULX_64 m (BArray256.get64 _P_mP 0));
      trace_h__H__MUL__XLOOP____mont_redM <-
      (trace_h__H__MUL__XLOOP____mont_redM ++
      [(Assert, (BArray128.is_init b_r 0 8))]);
      t <- (BArray128.get64 r 0);
      (of_0, t) <- (ADOX_64 t lo of_0);
      i <- 1;
      while ((i < 16)) {
        trace_h__H__MUL__XLOOP____mont_redM <-
        (trace_h__H__MUL__XLOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
        trace_h__H__MUL__XLOOP____mont_redM <-
        (trace_h__H__MUL__XLOOP____mont_redM ++
        [(Assert, (BArray128.is_init b_r (i * 8) 8))]);
        t <- (BArray128.get64 r i);
        (cf, t) <- (ADCX_64 t hi cf);
        trace_h__H__MUL__XLOOP____mont_redM <-
        (trace_h__H__MUL__XLOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
        (hi, lo) <- (MULX_64 m (BArray256.get64 _P_mP i));
        (of_0, t) <- (ADOX_64 t lo of_0);
        trace_h__H__MUL__XLOOP____mont_redM <-
        (trace_h__H__MUL__XLOOP____mont_redM ++
        [(Assert, ((0 <= ((i - 1) * 8)) /\ ((((i - 1) * 8) + 8) <= 128)))]);
        b_r <-
        (BArray128.set64d b_r ((i - 1) * 8) (W64.of_int 18446744073709551615)
        );
        r <- (BArray128.set64 r (i - 1) t);
        i <- (i + 1);
      }
      (cf, hi) <- (ADCX_64 hi _zero cf);
      (of_0, hi) <- (ADOX_64 hi _zero of_0);
      ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
      trace_h__H__MUL__XLOOP____mont_redM <-
      (trace_h__H__MUL__XLOOP____mont_redM ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int 16))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int 16))) * 8) + 8) <= 256)))]);
      (cf, hi) <-
      (adc_64 hi (BArray256.get64 a (W64.to_uint (k + (W64.of_int 16)))) cf);
      trace_h__H__MUL__XLOOP____mont_redM <-
      (trace_h__H__MUL__XLOOP____mont_redM ++
      [(Assert, ((0 <= ((16 - 1) * 8)) /\ ((((16 - 1) * 8) + 8) <= 128)))]);
      b_r <-
      (BArray128.set64d b_r ((16 - 1) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray128.set64 r (16 - 1) hi);
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + (W64.of_int 1));
    }
    trace_h__H__MUL__XLOOP____mont_redM <-
    (trace_h__H__MUL__XLOOP____mont_redM ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 256)))]);
    b_mP <- (SBArray256_128.get_sub64 b__P_mP 16);
    mP <- (SBArray256_128.get_sub64 _P_mP 16);
    b_param <- b_r;
    param <- r;
    b_param_0 <- b_mP;
    param_0 <- mP;
    param_1 <- c;
    (aux, aux_0, tmp__trace) <@ h__H__BN___cminusP_ (param, b_param, 
    param_0, b_param_0, param_1);
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__XLOOP____mont_redM <-
    (trace_h__H__MUL__XLOOP____mont_redM ++ tmp__trace);
    trace_h__H__MUL__XLOOP____mont_redM <-
    (trace_h__H__MUL__XLOOP____mont_redM ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    r <- result;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__XLOOP____mont_redM);
  }
  proc h__H__MUL__XREG____mulr_row0 (a:W64.t, b:BArray128.t, b_b:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:W64.t;
    var aux_0:W64.t;
    var aux_1:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_3:bool;
    var aux_5:bool;
    var b_t:BArray256.t;
    var cf:bool;
    var _zero:W64.t;
    var t:BArray256.t;
    var i:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__H__MUL__XREG____mulr_row0:trace;
    b_t <- witness;
    t <- witness;
    trace_h__H__MUL__XREG____mulr_row0 <- [];
    trace_h__H__MUL__XREG____mulr_row0 <-
    (trace_h__H__MUL__XREG____mulr_row0 ++
    [(Assert, (BArray128.is_init b_b 0 128))]);
    b_t <- (BArray256.init_arr (W8.of_int 0));
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    b_t <- (BArray256.set64d b_t 8 (W64.of_int 18446744073709551615));
    b_t <- (BArray256.set64d b_t 0 (W64.of_int 18446744073709551615));
    (aux, aux_0) <- (MULX_64 a (BArray128.get64 b 0));
    t <- (BArray256.set64 t 1 aux);
    t <- (BArray256.set64 t 0 aux_0);
    i <- 1;
    while ((i < 16)) {
      trace_h__H__MUL__XREG____mulr_row0 <-
      (trace_h__H__MUL__XREG____mulr_row0 ++
      [(Assert, ((0 <= ((i + 1) * 8)) /\ ((((i + 1) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____mulr_row0 <-
      (trace_h__H__MUL__XREG____mulr_row0 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      b_t <-
      (BArray256.set64d b_t ((i + 1) * 8) (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (MULX_64 a (BArray128.get64 b i));
      t <- (BArray256.set64 t (i + 1) aux_1);
      lo <- aux_2;
      trace_h__H__MUL__XREG____mulr_row0 <-
      (trace_h__H__MUL__XREG____mulr_row0 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____mulr_row0 <-
      (trace_h__H__MUL__XREG____mulr_row0 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____mulr_row0 <-
      (trace_h__H__MUL__XREG____mulr_row0 ++
      [(Assert, (BArray256.is_init b_t (i * 8) 8))]);
      b_t <-
      (BArray256.set64d b_t (i * 8) (W64.of_int 18446744073709551615));
      (aux_3, aux_4) <- (ADCX_64 (BArray256.get64 t i) lo cf);
      cf <- aux_3;
      t <- (BArray256.set64 t i aux_4);
      i <- (i + 1);
    }
    trace_h__H__MUL__XREG____mulr_row0 <-
    (trace_h__H__MUL__XREG____mulr_row0 ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____mulr_row0 <-
    (trace_h__H__MUL__XREG____mulr_row0 ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____mulr_row0 <-
    (trace_h__H__MUL__XREG____mulr_row0 ++
    [(Assert, (BArray256.is_init b_t (16 * 8) 8))]);
    b_t <- (BArray256.set64d b_t (16 * 8) (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADCX_64 (BArray256.get64 t 16) _zero cf);
    cf <- aux_5;
    t <- (BArray256.set64 t 16 aux_6);
    return (t, b_t, trace_h__H__MUL__XREG____mulr_row0);
  }
  proc h__H__MUL__XREG____mulr_rowk (k:int, t:BArray256.t, b_t:BArray256.t,
                                     a:W64.t, b:BArray128.t, b_b:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux_0:W64.t;
    var aux_2:W64.t;
    var aux_3:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_8:W64.t;
    var aux_10:W64.t;
    var aux:bool;
    var aux_1:bool;
    var aux_5:bool;
    var aux_7:bool;
    var aux_9:bool;
    var inc:int;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var i:int;
    var hi:W64.t;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__H__MUL__XREG____mulr_rowk:trace;
    trace_h__H__MUL__XREG____mulr_rowk <- [];
    trace_h__H__MUL__XREG____mulr_rowk <-
    (trace_h__H__MUL__XREG____mulr_rowk ++
    [(Assert,
     ((((1 <= k) /\ (k < 16)) /\ (BArray256.is_init b_t 0 (8 * (k + 16)))) /\
     (BArray128.is_init b_b 0 128)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    inc <- (16 - 1);
    i <- 0;
    while ((i < inc)) {
      trace_h__H__MUL__XREG____mulr_rowk <-
      (trace_h__H__MUL__XREG____mulr_rowk ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      (hi, lo) <- (MULX_64 a (BArray128.get64 b i));
      trace_h__H__MUL__XREG____mulr_rowk <-
      (trace_h__H__MUL__XREG____mulr_rowk ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____mulr_rowk <-
      (trace_h__H__MUL__XREG____mulr_rowk ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____mulr_rowk <-
      (trace_h__H__MUL__XREG____mulr_rowk ++
      [(Assert, (BArray256.is_init b_t ((k + i) * 8) 8))]);
      b_t <-
      (BArray256.set64d b_t ((k + i) * 8) (W64.of_int 18446744073709551615));
      (aux, aux_0) <- (ADOX_64 (BArray256.get64 t (k + i)) lo of_0);
      of_0 <- aux;
      t <- (BArray256.set64 t (k + i) aux_0);
      trace_h__H__MUL__XREG____mulr_rowk <-
      (trace_h__H__MUL__XREG____mulr_rowk ++
      [(Assert,
       ((0 <= (((k + i) + 1) * 8)) /\ (((((k + i) + 1) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____mulr_rowk <-
      (trace_h__H__MUL__XREG____mulr_rowk ++
      [(Assert,
       ((0 <= (((k + i) + 1) * 8)) /\ (((((k + i) + 1) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____mulr_rowk <-
      (trace_h__H__MUL__XREG____mulr_rowk ++
      [(Assert, (BArray256.is_init b_t (((k + i) + 1) * 8) 8))]);
      b_t <-
      (BArray256.set64d b_t (((k + i) + 1) * 8)
      (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (ADCX_64 (BArray256.get64 t ((k + i) + 1)) hi cf);
      cf <- aux_1;
      t <- (BArray256.set64 t ((k + i) + 1) aux_2);
      i <- (i + 1);
    }
    trace_h__H__MUL__XREG____mulr_rowk <-
    (trace_h__H__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 16) * 8)) /\ ((((k + 16) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____mulr_rowk <-
    (trace_h__H__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((16 - 1) * 8)) /\ ((((16 - 1) * 8) + 8) <= 128)))]);
    b_t <-
    (BArray256.set64d b_t ((k + 16) * 8) (W64.of_int 18446744073709551615));
    (aux_3, aux_4) <- (MULX_64 a (BArray128.get64 b (16 - 1)));
    t <- (BArray256.set64 t (k + 16) aux_3);
    lo <- aux_4;
    trace_h__H__MUL__XREG____mulr_rowk <-
    (trace_h__H__MUL__XREG____mulr_rowk ++
    [(Assert,
     ((0 <= (((k + 16) - 1) * 8)) /\ (((((k + 16) - 1) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____mulr_rowk <-
    (trace_h__H__MUL__XREG____mulr_rowk ++
    [(Assert,
     ((0 <= (((k + 16) - 1) * 8)) /\ (((((k + 16) - 1) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____mulr_rowk <-
    (trace_h__H__MUL__XREG____mulr_rowk ++
    [(Assert, (BArray256.is_init b_t (((k + 16) - 1) * 8) 8))]);
    b_t <-
    (BArray256.set64d b_t (((k + 16) - 1) * 8)
    (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADOX_64 (BArray256.get64 t ((k + 16) - 1)) lo of_0);
    of_0 <- aux_5;
    t <- (BArray256.set64 t ((k + 16) - 1) aux_6);
    trace_h__H__MUL__XREG____mulr_rowk <-
    (trace_h__H__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 16) * 8)) /\ ((((k + 16) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____mulr_rowk <-
    (trace_h__H__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 16) * 8)) /\ ((((k + 16) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____mulr_rowk <-
    (trace_h__H__MUL__XREG____mulr_rowk ++
    [(Assert, (BArray256.is_init b_t ((k + 16) * 8) 8))]);
    b_t <-
    (BArray256.set64d b_t ((k + 16) * 8) (W64.of_int 18446744073709551615));
    (aux_7, aux_8) <- (ADCX_64 (BArray256.get64 t (k + 16)) _zero cf);
    cf <- aux_7;
    t <- (BArray256.set64 t (k + 16) aux_8);
    trace_h__H__MUL__XREG____mulr_rowk <-
    (trace_h__H__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 16) * 8)) /\ ((((k + 16) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____mulr_rowk <-
    (trace_h__H__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 16) * 8)) /\ ((((k + 16) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____mulr_rowk <-
    (trace_h__H__MUL__XREG____mulr_rowk ++
    [(Assert, (BArray256.is_init b_t ((k + 16) * 8) 8))]);
    b_t <-
    (BArray256.set64d b_t ((k + 16) * 8) (W64.of_int 18446744073709551615));
    (aux_9, aux_10) <- (ADOX_64 (BArray256.get64 t (k + 16)) _zero of_0);
    of_0 <- aux_9;
    t <- (BArray256.set64 t (k + 16) aux_10);
    return (t, b_t, trace_h__H__MUL__XREG____mulr_rowk);
  }
  proc h__H__MUL__XREG___os_muln (r:BArray256.t, b_r:BArray256.t,
                                  a:BArray128.t, b_a:BArray128.t,
                                  b:BArray128.t, b_b:BArray128.t) : BArray256.t *
                                                                    BArray256.t *
                                                                    trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var inc:int;
    var ak:W64.t;
    var param:W64.t;
    var param_0:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var b_t:BArray256.t;
    var t:BArray256.t;
    var k:int;
    var param_1:int;
    var b_param:BArray256.t;
    var param_2:BArray256.t;
    var param_3:W64.t;
    var param_4:BArray128.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var trace_h__H__MUL__XREG___os_muln:trace;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_t <- witness;
    param_0 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    t <- witness;
    trace_h__H__MUL__XREG___os_muln <- [];
    trace_h__H__MUL__XREG___os_muln <-
    (trace_h__H__MUL__XREG___os_muln ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    ak <- (BArray128.get64 a 0);
    param <- ak;
    param_0 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__XREG____mulr_row0 (param, 
    param_0, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__XREG___os_muln <-
    (trace_h__H__MUL__XREG___os_muln ++ tmp__trace);
    trace_h__H__MUL__XREG___os_muln <-
    (trace_h__H__MUL__XREG___os_muln ++
    [(Assert, (BArray256.is_init b_result 0 136))]);
    b_t <- b_result;
    t <- result;
    trace_h__H__MUL__XREG___os_muln <-
    (trace_h__H__MUL__XREG___os_muln ++
    [(Assert, (BArray256.is_init b_t 0 8))]);
    b_r <- (BArray256.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 0 (BArray256.get64 t 0));
    k <- 1;
    while ((k < 16)) {
      trace_h__H__MUL__XREG___os_muln <-
      (trace_h__H__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 128)))]);
      ak <- (BArray128.get64 a k);
      param_1 <- k;
      b_param <- b_t;
      param_2 <- t;
      param_3 <- ak;
      param_4 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__H__MUL__XREG____mulr_rowk (param_1,
      param_2, b_param, param_3, param_4,
      (BArray128.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__H__MUL__XREG___os_muln <-
      (trace_h__H__MUL__XREG___os_muln ++ tmp__trace);
      trace_h__H__MUL__XREG___os_muln <-
      (trace_h__H__MUL__XREG___os_muln ++
      [(Assert, (BArray256.is_init b_result_0 0 (8 * ((param_1 + 16) + 1))))]);
      b_t <- b_result_0;
      t <- result_0;
      trace_h__H__MUL__XREG___os_muln <-
      (trace_h__H__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG___os_muln <-
      (trace_h__H__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG___os_muln <-
      (trace_h__H__MUL__XREG___os_muln ++
      [(Assert, (BArray256.is_init b_t (k * 8) 8))]);
      b_r <-
      (BArray256.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r k (BArray256.get64 t k));
      k <- (k + 1);
    }
    inc <- (2 * 16);
    k <- 16;
    while ((k < inc)) {
      trace_h__H__MUL__XREG___os_muln <-
      (trace_h__H__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG___os_muln <-
      (trace_h__H__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG___os_muln <-
      (trace_h__H__MUL__XREG___os_muln ++
      [(Assert, (BArray256.is_init b_t (k * 8) 8))]);
      b_r <-
      (BArray256.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r k (BArray256.get64 t k));
      k <- (k + 1);
    }
    return (r, b_r, trace_h__H__MUL__XREG___os_muln);
  }
  proc h__H__MUL__XREG___os_muln_ (r:BArray256.t, b_r:BArray256.t,
                                   a:BArray128.t, b_a:BArray128.t,
                                   b:BArray128.t, b_b:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__MUL__XREG___os_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__MUL__XREG___os_muln_ <- [];
    trace_h__H__MUL__XREG___os_muln_ <-
    (trace_h__H__MUL__XREG___os_muln_ ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__XREG___os_muln (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__XREG___os_muln_ <-
    (trace_h__H__MUL__XREG___os_muln_ ++ tmp__trace);
    trace_h__H__MUL__XREG___os_muln_ <-
    (trace_h__H__MUL__XREG___os_muln_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__XREG___os_muln_);
  }
  proc h__H__MUL__XREG____sqrr_row0 (a:BArray128.t, b_a:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:W64.t;
    var aux_0:W64.t;
    var aux_1:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_3:bool;
    var aux_5:bool;
    var b_t:BArray256.t;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var t:BArray256.t;
    var j:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__H__MUL__XREG____sqrr_row0:trace;
    b_t <- witness;
    t <- witness;
    trace_h__H__MUL__XREG____sqrr_row0 <- [];
    trace_h__H__MUL__XREG____sqrr_row0 <-
    (trace_h__H__MUL__XREG____sqrr_row0 ++
    [(Assert, ((2 <= 16) /\ (BArray128.is_init b_a 0 128)))]);
    b_t <- (BArray256.init_arr (W8.of_int 0));
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    ai <- (BArray128.get64 a 0);
    b_t <- (BArray256.set64d b_t 16 (W64.of_int 18446744073709551615));
    b_t <- (BArray256.set64d b_t 8 (W64.of_int 18446744073709551615));
    (aux, aux_0) <- (MULX_64 ai (BArray128.get64 a 1));
    t <- (BArray256.set64 t 2 aux);
    t <- (BArray256.set64 t 1 aux_0);
    j <- 2;
    while ((j < 16)) {
      trace_h__H__MUL__XREG____sqrr_row0 <-
      (trace_h__H__MUL__XREG____sqrr_row0 ++
      [(Assert, ((0 <= ((j + 1) * 8)) /\ ((((j + 1) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____sqrr_row0 <-
      (trace_h__H__MUL__XREG____sqrr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 128)))]);
      b_t <-
      (BArray256.set64d b_t ((j + 1) * 8) (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (MULX_64 ai (BArray128.get64 a j));
      t <- (BArray256.set64 t (j + 1) aux_1);
      lo <- aux_2;
      trace_h__H__MUL__XREG____sqrr_row0 <-
      (trace_h__H__MUL__XREG____sqrr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____sqrr_row0 <-
      (trace_h__H__MUL__XREG____sqrr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____sqrr_row0 <-
      (trace_h__H__MUL__XREG____sqrr_row0 ++
      [(Assert, (BArray256.is_init b_t (j * 8) 8))]);
      b_t <-
      (BArray256.set64d b_t (j * 8) (W64.of_int 18446744073709551615));
      (aux_3, aux_4) <- (ADCX_64 (BArray256.get64 t j) lo cf);
      cf <- aux_3;
      t <- (BArray256.set64 t j aux_4);
      j <- (j + 1);
    }
    trace_h__H__MUL__XREG____sqrr_row0 <-
    (trace_h__H__MUL__XREG____sqrr_row0 ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____sqrr_row0 <-
    (trace_h__H__MUL__XREG____sqrr_row0 ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____sqrr_row0 <-
    (trace_h__H__MUL__XREG____sqrr_row0 ++
    [(Assert, (BArray256.is_init b_t (16 * 8) 8))]);
    b_t <- (BArray256.set64d b_t (16 * 8) (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADCX_64 (BArray256.get64 t 16) _zero cf);
    cf <- aux_5;
    t <- (BArray256.set64 t 16 aux_6);
    return (t, b_t, trace_h__H__MUL__XREG____sqrr_row0);
  }
  proc h__H__MUL__XREG____sqrr_rowi (i:int, t:BArray256.t, b_t:BArray256.t,
                                     a:BArray128.t, b_a:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux_0:W64.t;
    var aux_2:W64.t;
    var aux_3:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_8:W64.t;
    var aux_10:W64.t;
    var aux:bool;
    var aux_1:bool;
    var aux_5:bool;
    var aux_7:bool;
    var aux_9:bool;
    var inc:int;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var j:int;
    var hi:W64.t;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__H__MUL__XREG____sqrr_rowi:trace;
    trace_h__H__MUL__XREG____sqrr_rowi <- [];
    trace_h__H__MUL__XREG____sqrr_rowi <-
    (trace_h__H__MUL__XREG____sqrr_rowi ++
    [(Assert,
     ((((1 <= i) /\ (i < (16 - 1))) /\
      (BArray256.is_init b_t 8 (8 * ((i + 16) - 1)))) /\
     (BArray128.is_init b_a 0 128)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    trace_h__H__MUL__XREG____sqrr_rowi <-
    (trace_h__H__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
    ai <- (BArray128.get64 a i);
    inc <- (16 - 1);
    j <- (i + 1);
    while ((j < inc)) {
      trace_h__H__MUL__XREG____sqrr_rowi <-
      (trace_h__H__MUL__XREG____sqrr_rowi ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 128)))]);
      (hi, lo) <- (MULX_64 ai (BArray128.get64 a j));
      trace_h__H__MUL__XREG____sqrr_rowi <-
      (trace_h__H__MUL__XREG____sqrr_rowi ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____sqrr_rowi <-
      (trace_h__H__MUL__XREG____sqrr_rowi ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____sqrr_rowi <-
      (trace_h__H__MUL__XREG____sqrr_rowi ++
      [(Assert, (BArray256.is_init b_t ((i + j) * 8) 8))]);
      b_t <-
      (BArray256.set64d b_t ((i + j) * 8) (W64.of_int 18446744073709551615));
      (aux, aux_0) <- (ADOX_64 (BArray256.get64 t (i + j)) lo of_0);
      of_0 <- aux;
      t <- (BArray256.set64 t (i + j) aux_0);
      trace_h__H__MUL__XREG____sqrr_rowi <-
      (trace_h__H__MUL__XREG____sqrr_rowi ++
      [(Assert,
       ((0 <= (((i + j) + 1) * 8)) /\ (((((i + j) + 1) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____sqrr_rowi <-
      (trace_h__H__MUL__XREG____sqrr_rowi ++
      [(Assert,
       ((0 <= (((i + j) + 1) * 8)) /\ (((((i + j) + 1) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____sqrr_rowi <-
      (trace_h__H__MUL__XREG____sqrr_rowi ++
      [(Assert, (BArray256.is_init b_t (((i + j) + 1) * 8) 8))]);
      b_t <-
      (BArray256.set64d b_t (((i + j) + 1) * 8)
      (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (ADCX_64 (BArray256.get64 t ((i + j) + 1)) hi cf);
      cf <- aux_1;
      t <- (BArray256.set64 t ((i + j) + 1) aux_2);
      j <- (j + 1);
    }
    trace_h__H__MUL__XREG____sqrr_rowi <-
    (trace_h__H__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 16) * 8)) /\ ((((i + 16) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____sqrr_rowi <-
    (trace_h__H__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((16 - 1) * 8)) /\ ((((16 - 1) * 8) + 8) <= 128)))]);
    b_t <-
    (BArray256.set64d b_t ((i + 16) * 8) (W64.of_int 18446744073709551615));
    (aux_3, aux_4) <- (MULX_64 ai (BArray128.get64 a (16 - 1)));
    t <- (BArray256.set64 t (i + 16) aux_3);
    lo <- aux_4;
    trace_h__H__MUL__XREG____sqrr_rowi <-
    (trace_h__H__MUL__XREG____sqrr_rowi ++
    [(Assert,
     ((0 <= (((i + 16) - 1) * 8)) /\ (((((i + 16) - 1) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____sqrr_rowi <-
    (trace_h__H__MUL__XREG____sqrr_rowi ++
    [(Assert,
     ((0 <= (((i + 16) - 1) * 8)) /\ (((((i + 16) - 1) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____sqrr_rowi <-
    (trace_h__H__MUL__XREG____sqrr_rowi ++
    [(Assert, (BArray256.is_init b_t (((i + 16) - 1) * 8) 8))]);
    b_t <-
    (BArray256.set64d b_t (((i + 16) - 1) * 8)
    (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADOX_64 (BArray256.get64 t ((i + 16) - 1)) lo of_0);
    of_0 <- aux_5;
    t <- (BArray256.set64 t ((i + 16) - 1) aux_6);
    trace_h__H__MUL__XREG____sqrr_rowi <-
    (trace_h__H__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 16) * 8)) /\ ((((i + 16) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____sqrr_rowi <-
    (trace_h__H__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 16) * 8)) /\ ((((i + 16) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____sqrr_rowi <-
    (trace_h__H__MUL__XREG____sqrr_rowi ++
    [(Assert, (BArray256.is_init b_t ((i + 16) * 8) 8))]);
    b_t <-
    (BArray256.set64d b_t ((i + 16) * 8) (W64.of_int 18446744073709551615));
    (aux_7, aux_8) <- (ADCX_64 (BArray256.get64 t (i + 16)) _zero cf);
    cf <- aux_7;
    t <- (BArray256.set64 t (i + 16) aux_8);
    trace_h__H__MUL__XREG____sqrr_rowi <-
    (trace_h__H__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 16) * 8)) /\ ((((i + 16) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____sqrr_rowi <-
    (trace_h__H__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 16) * 8)) /\ ((((i + 16) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____sqrr_rowi <-
    (trace_h__H__MUL__XREG____sqrr_rowi ++
    [(Assert, (BArray256.is_init b_t ((i + 16) * 8) 8))]);
    b_t <-
    (BArray256.set64d b_t ((i + 16) * 8) (W64.of_int 18446744073709551615));
    (aux_9, aux_10) <- (ADOX_64 (BArray256.get64 t (i + 16)) _zero of_0);
    of_0 <- aux_9;
    t <- (BArray256.set64 t (i + 16) aux_10);
    return (t, b_t, trace_h__H__MUL__XREG____sqrr_rowi);
  }
  proc h__H__MUL__XREG____sqrr_diag (r:BArray256.t, b_r:BArray256.t,
                                     t:BArray256.t, b_t:BArray256.t,
                                     a:BArray128.t, b_a:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var inc:int;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var w:int;
    var x:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__H__MUL__XREG____sqrr_diag:trace;
    trace_h__H__MUL__XREG____sqrr_diag <- [];
    trace_h__H__MUL__XREG____sqrr_diag <-
    (trace_h__H__MUL__XREG____sqrr_diag ++
    [(Assert,
     ((((2 <= 16) /\ (BArray256.is_init b_r 8 176)) /\
      (BArray256.is_init b_t 8 240)) /\
     (BArray128.is_init b_a 0 128)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    ai <- (BArray128.get64 a 0);
    (hi, lo) <- (MULX_64 ai (BArray128.get64 a 0));
    b_r <- (BArray256.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 0 lo);
    w <- 1;
    if (((w + 10) <= (2 * 16))) {
      trace_h__H__MUL__XREG____sqrr_diag <-
      (trace_h__H__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____sqrr_diag <-
      (trace_h__H__MUL__XREG____sqrr_diag ++
      [(Assert, (BArray256.is_init b_r (w * 8) 8))]);
      x <- (BArray256.get64 r w);
    } else {
      trace_h__H__MUL__XREG____sqrr_diag <-
      (trace_h__H__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____sqrr_diag <-
      (trace_h__H__MUL__XREG____sqrr_diag ++
      [(Assert, (BArray256.is_init b_t (w * 8) 8))]);
      x <- (BArray256.get64 t w);
    }
    (cf, x) <- (ADCX_64 x x cf);
    (of_0, x) <- (ADOX_64 x hi of_0);
    b_r <- (BArray256.set64d b_r 8 (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 1 x);
    inc <- (16 - 1);
    i <- 1;
    while ((i < inc)) {
      trace_h__H__MUL__XREG____sqrr_diag <-
      (trace_h__H__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      ai <- (BArray128.get64 a i);
      trace_h__H__MUL__XREG____sqrr_diag <-
      (trace_h__H__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      (hi, lo) <- (MULX_64 ai (BArray128.get64 a i));
      w <- (2 * i);
      if (((w + 10) <= (2 * 16))) {
        trace_h__H__MUL__XREG____sqrr_diag <-
        (trace_h__H__MUL__XREG____sqrr_diag ++
        [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 256)))]);
        trace_h__H__MUL__XREG____sqrr_diag <-
        (trace_h__H__MUL__XREG____sqrr_diag ++
        [(Assert, (BArray256.is_init b_r (w * 8) 8))]);
        x <- (BArray256.get64 r w);
      } else {
        trace_h__H__MUL__XREG____sqrr_diag <-
        (trace_h__H__MUL__XREG____sqrr_diag ++
        [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 256)))]);
        trace_h__H__MUL__XREG____sqrr_diag <-
        (trace_h__H__MUL__XREG____sqrr_diag ++
        [(Assert, (BArray256.is_init b_t (w * 8) 8))]);
        x <- (BArray256.get64 t w);
      }
      (cf, x) <- (ADCX_64 x x cf);
      (of_0, x) <- (ADOX_64 x lo of_0);
      trace_h__H__MUL__XREG____sqrr_diag <-
      (trace_h__H__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= ((2 * i) * 8)) /\ ((((2 * i) * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r ((2 * i) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r (2 * i) x);
      w <- ((2 * i) + 1);
      if (((w + 10) <= (2 * 16))) {
        trace_h__H__MUL__XREG____sqrr_diag <-
        (trace_h__H__MUL__XREG____sqrr_diag ++
        [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 256)))]);
        trace_h__H__MUL__XREG____sqrr_diag <-
        (trace_h__H__MUL__XREG____sqrr_diag ++
        [(Assert, (BArray256.is_init b_r (w * 8) 8))]);
        x <- (BArray256.get64 r w);
      } else {
        trace_h__H__MUL__XREG____sqrr_diag <-
        (trace_h__H__MUL__XREG____sqrr_diag ++
        [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 256)))]);
        trace_h__H__MUL__XREG____sqrr_diag <-
        (trace_h__H__MUL__XREG____sqrr_diag ++
        [(Assert, (BArray256.is_init b_t (w * 8) 8))]);
        x <- (BArray256.get64 t w);
      }
      (cf, x) <- (ADCX_64 x x cf);
      (of_0, x) <- (ADOX_64 x hi of_0);
      trace_h__H__MUL__XREG____sqrr_diag <-
      (trace_h__H__MUL__XREG____sqrr_diag ++
      [(Assert,
       ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (((2 * i) + 1) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r ((2 * i) + 1) x);
      i <- (i + 1);
    }
    trace_h__H__MUL__XREG____sqrr_diag <-
    (trace_h__H__MUL__XREG____sqrr_diag ++
    [(Assert, ((0 <= ((16 - 1) * 8)) /\ ((((16 - 1) * 8) + 8) <= 128)))]);
    ai <- (BArray128.get64 a (16 - 1));
    trace_h__H__MUL__XREG____sqrr_diag <-
    (trace_h__H__MUL__XREG____sqrr_diag ++
    [(Assert, ((0 <= ((16 - 1) * 8)) /\ ((((16 - 1) * 8) + 8) <= 128)))]);
    (hi, lo) <- (MULX_64 ai (BArray128.get64 a (16 - 1)));
    trace_h__H__MUL__XREG____sqrr_diag <-
    (trace_h__H__MUL__XREG____sqrr_diag ++
    [(Assert,
     ((0 <= (((2 * 16) - 2) * 8)) /\ (((((2 * 16) - 2) * 8) + 8) <= 256)))]);
    trace_h__H__MUL__XREG____sqrr_diag <-
    (trace_h__H__MUL__XREG____sqrr_diag ++
    [(Assert, (BArray256.is_init b_t (((2 * 16) - 2) * 8) 8))]);
    x <- (BArray256.get64 t ((2 * 16) - 2));
    (cf, x) <- (ADCX_64 x x cf);
    (of_0, x) <- (ADOX_64 x lo of_0);
    trace_h__H__MUL__XREG____sqrr_diag <-
    (trace_h__H__MUL__XREG____sqrr_diag ++
    [(Assert,
     ((0 <= (((2 * 16) - 2) * 8)) /\ (((((2 * 16) - 2) * 8) + 8) <= 256)))]);
    b_r <-
    (BArray256.set64d b_r (((2 * 16) - 2) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r ((2 * 16) - 2) x);
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__H__MUL__XREG____sqrr_diag <-
    (trace_h__H__MUL__XREG____sqrr_diag ++
    [(Assert,
     ((0 <= (((2 * 16) - 1) * 8)) /\ (((((2 * 16) - 1) * 8) + 8) <= 256)))]);
    b_r <-
    (BArray256.set64d b_r (((2 * 16) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r ((2 * 16) - 1) hi);
    return (r, b_r, trace_h__H__MUL__XREG____sqrr_diag);
  }
  proc h__H__MUL__XREG___os_sqrn (r:BArray256.t, b_r:BArray256.t,
                                  a:BArray128.t, b_a:BArray128.t) : BArray256.t *
                                                                    BArray256.t *
                                                                    trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var aux_3:BArray256.t;
    var aux_4:BArray256.t;
    var inc:int;
    var inc_0:int;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var param:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var b_t:BArray256.t;
    var t:BArray256.t;
    var w:int;
    var i:int;
    var param_0:int;
    var b_param:BArray256.t;
    var param_1:BArray256.t;
    var param_2:BArray128.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var b_param_0:BArray256.t;
    var param_3:BArray256.t;
    var b_param_1:BArray256.t;
    var param_4:BArray256.t;
    var param_5:BArray128.t;
    var result_1:BArray256.t;
    var b_result_1:BArray256.t;
    var trace_h__H__MUL__XREG___os_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_t <- witness;
    param <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    t <- witness;
    trace_h__H__MUL__XREG___os_sqrn <- [];
    trace_h__H__MUL__XREG___os_sqrn <-
    (trace_h__H__MUL__XREG___os_sqrn ++
    [(Assert, (BArray128.is_init b_a 0 128))]);
    if ((16 = 1)) {
      trace_h__H__MUL__XREG___os_sqrn <-
      (trace_h__H__MUL__XREG___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 128)))]);
      ai <- (BArray128.get64 a 0);
      trace_h__H__MUL__XREG___os_sqrn <-
      (trace_h__H__MUL__XREG___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 128)))]);
      (hi, lo) <- (MULX_64 ai (BArray128.get64 a 0));
      trace_h__H__MUL__XREG___os_sqrn <-
      (trace_h__H__MUL__XREG___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (0 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r 0 lo);
      trace_h__H__MUL__XREG___os_sqrn <-
      (trace_h__H__MUL__XREG___os_sqrn ++
      [(Assert, ((0 <= (1 * 8)) /\ (((1 * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (1 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r 1 hi);
    } else {
      param <- a;
      (aux, aux_0, tmp__trace) <@ h__H__MUL__XREG____sqrr_row0 (param,
      (BArray128.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__H__MUL__XREG___os_sqrn <-
      (trace_h__H__MUL__XREG___os_sqrn ++ tmp__trace);
      trace_h__H__MUL__XREG___os_sqrn <-
      (trace_h__H__MUL__XREG___os_sqrn ++
      [(Assert, (BArray256.is_init b_result 8 128))]);
      b_t <- b_result;
      t <- result;
      w <- 1;
      while ((w < 3)) {
        if (((w + 10) <= (2 * 16))) {
          trace_h__H__MUL__XREG___os_sqrn <-
          (trace_h__H__MUL__XREG___os_sqrn ++
          [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 256)))]);
          trace_h__H__MUL__XREG___os_sqrn <-
          (trace_h__H__MUL__XREG___os_sqrn ++
          [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 256)))]);
          trace_h__H__MUL__XREG___os_sqrn <-
          (trace_h__H__MUL__XREG___os_sqrn ++
          [(Assert, (BArray256.is_init b_t (w * 8) 8))]);
          b_r <-
          (BArray256.set64d b_r (w * 8) (W64.of_int 18446744073709551615));
          r <- (BArray256.set64 r w (BArray256.get64 t w));
        } else {
          
        }
        w <- (w + 1);
      }
      inc <- (16 - 1);
      i <- 1;
      while ((i < inc)) {
        param_0 <- i;
        b_param <- b_t;
        param_1 <- t;
        param_2 <- a;
        (aux_1, aux_2, tmp__trace) <@ h__H__MUL__XREG____sqrr_rowi (param_0,
        param_1, b_param, param_2, (BArray128.init_arr (W8.of_int 255)));
        result_0 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__H__MUL__XREG___os_sqrn <-
        (trace_h__H__MUL__XREG___os_sqrn ++ tmp__trace);
        trace_h__H__MUL__XREG___os_sqrn <-
        (trace_h__H__MUL__XREG___os_sqrn ++
        [(Assert, (BArray256.is_init b_result_0 8 (8 * (param_0 + 16))))]);
        b_t <- b_result_0;
        t <- result_0;
        inc_0 <- ((2 * i) + 3);
        w <- ((2 * i) + 1);
        while ((w < inc_0)) {
          if (((w + 10) <= (2 * 16))) {
            trace_h__H__MUL__XREG___os_sqrn <-
            (trace_h__H__MUL__XREG___os_sqrn ++
            [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 256)))]);
            trace_h__H__MUL__XREG___os_sqrn <-
            (trace_h__H__MUL__XREG___os_sqrn ++
            [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 256)))]);
            trace_h__H__MUL__XREG___os_sqrn <-
            (trace_h__H__MUL__XREG___os_sqrn ++
            [(Assert, (BArray256.is_init b_t (w * 8) 8))]);
            b_r <-
            (BArray256.set64d b_r (w * 8) (W64.of_int 18446744073709551615));
            r <- (BArray256.set64 r w (BArray256.get64 t w));
          } else {
            
          }
          w <- (w + 1);
        }
        i <- (i + 1);
      }
      b_param_0 <- b_r;
      param_3 <- r;
      b_param_1 <- b_t;
      param_4 <- t;
      param_5 <- a;
      (aux_3, aux_4, tmp__trace) <@ h__H__MUL__XREG____sqrr_diag (param_3,
      b_param_0, param_4, b_param_1, param_5,
      (BArray128.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__H__MUL__XREG___os_sqrn <-
      (trace_h__H__MUL__XREG___os_sqrn ++ tmp__trace);
      trace_h__H__MUL__XREG___os_sqrn <-
      (trace_h__H__MUL__XREG___os_sqrn ++
      [(Assert, (BArray256.is_init b_result_1 0 256))]);
      b_r <- (BArray256.init_arr (W8.of_int 255));
      r <- result_1;
    }
    return (r, b_r, trace_h__H__MUL__XREG___os_sqrn);
  }
  proc h__H__MUL__XREG___os_sqrn_ (r:BArray256.t, b_r:BArray256.t,
                                   a:BArray128.t, b_a:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__MUL__XREG___os_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__H__MUL__XREG___os_sqrn_ <- [];
    trace_h__H__MUL__XREG___os_sqrn_ <-
    (trace_h__H__MUL__XREG___os_sqrn_ ++
    [(Assert, (BArray128.is_init b_a 0 128))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__H__MUL__XREG___os_sqrn (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL__XREG___os_sqrn_ <-
    (trace_h__H__MUL__XREG___os_sqrn_ ++ tmp__trace);
    trace_h__H__MUL__XREG___os_sqrn_ <-
    (trace_h__H__MUL__XREG___os_sqrn_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL__XREG___os_sqrn_);
  }
  proc h__H__MUL__XREG____mont_redM (r:BArray128.t, b_r:BArray128.t,
                                     a:BArray256.t, b_a:BArray256.t,
                                     _P_mP:BArray256.t, b__P_mP:BArray256.t,
                                     _U0:W64.t) : BArray128.t * BArray128.t *
                                                  trace = {
    var aux_0:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_8:W64.t;
    var aux:bool;
    var aux_1:bool;
    var aux_3:bool;
    var aux_5:bool;
    var aux_7:bool;
    var b_w:BArray256.t;
    var b_s:BArray128.t;
    var i:int;
    var w:BArray256.t;
    var c:W64.t;
    var k:int;
    var m:W64.t;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var s:BArray128.t;
    var x:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var  _12:bool;
    var  _13:W64.t;
    var trace_h__H__MUL__XREG____mont_redM:trace;
    b_s <- witness;
    b_w <- witness;
    s <- witness;
    w <- witness;
    trace_h__H__MUL__XREG____mont_redM <- [];
    trace_h__H__MUL__XREG____mont_redM <-
    (trace_h__H__MUL__XREG____mont_redM ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b__P_mP 0 256)))]);
    b_w <- (BArray256.init_arr (W8.of_int 0));
    b_s <- (BArray128.init_arr (W8.of_int 0));
    i <- 0;
    while ((i < 16)) {
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      b_w <-
      (BArray256.set64d b_w (i * 8) (W64.of_int 18446744073709551615));
      w <- (BArray256.set64 w i (BArray256.get64 a i));
      i <- (i + 1);
    }
    c <- (W64.of_int 0);
    k <- 0;
    while ((k < 16)) {
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, (BArray256.is_init b_w (k * 8) 8))]);
      m <- (BArray256.get64 w k);
      m <- (m * _U0);
      (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
      (hi, lo) <- (MULX_64 m (BArray256.get64 _P_mP 0));
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, (BArray256.is_init b_w (k * 8) 8))]);
      b_w <-
      (BArray256.set64d b_w (k * 8) (W64.of_int 18446744073709551615));
      (aux, aux_0) <- (ADOX_64 (BArray256.get64 w k) lo of_0);
      of_0 <- aux;
      w <- (BArray256.set64 w k aux_0);
      i <- 1;
      while ((i < 16)) {
        trace_h__H__MUL__XREG____mont_redM <-
        (trace_h__H__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 256)))]);
        trace_h__H__MUL__XREG____mont_redM <-
        (trace_h__H__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 256)))]);
        trace_h__H__MUL__XREG____mont_redM <-
        (trace_h__H__MUL__XREG____mont_redM ++
        [(Assert, (BArray256.is_init b_w ((k + i) * 8) 8))]);
        b_w <-
        (BArray256.set64d b_w ((k + i) * 8) (W64.of_int 18446744073709551615)
        );
        (aux_1, aux_2) <- (ADCX_64 (BArray256.get64 w (k + i)) hi cf);
        cf <- aux_1;
        w <- (BArray256.set64 w (k + i) aux_2);
        trace_h__H__MUL__XREG____mont_redM <-
        (trace_h__H__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
        (hi, lo) <- (MULX_64 m (BArray256.get64 _P_mP i));
        trace_h__H__MUL__XREG____mont_redM <-
        (trace_h__H__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 256)))]);
        trace_h__H__MUL__XREG____mont_redM <-
        (trace_h__H__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 256)))]);
        trace_h__H__MUL__XREG____mont_redM <-
        (trace_h__H__MUL__XREG____mont_redM ++
        [(Assert, (BArray256.is_init b_w ((k + i) * 8) 8))]);
        b_w <-
        (BArray256.set64d b_w ((k + i) * 8) (W64.of_int 18446744073709551615)
        );
        (aux_3, aux_4) <- (ADOX_64 (BArray256.get64 w (k + i)) lo of_0);
        of_0 <- aux_3;
        w <- (BArray256.set64 w (k + i) aux_4);
        i <- (i + 1);
      }
      (cf, hi) <- (ADCX_64 hi _zero cf);
      (of_0, hi) <- (ADOX_64 hi _zero of_0);
      if ((k = 0)) {
        trace_h__H__MUL__XREG____mont_redM <-
        (trace_h__H__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 8) <= 256)))]);
        (cf, hi) <- (adc_64 hi (BArray256.get64 a 16) false);
      } else {
        ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
        trace_h__H__MUL__XREG____mont_redM <-
        (trace_h__H__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + 16) * 8)) /\ ((((k + 16) * 8) + 8) <= 256)))]);
        (cf, hi) <- (adc_64 hi (BArray256.get64 a (k + 16)) cf);
      }
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((k + 16) * 8)) /\ ((((k + 16) * 8) + 8) <= 256)))]);
      b_w <-
      (BArray256.set64d b_w ((k + 16) * 8) (W64.of_int 18446744073709551615));
      w <- (BArray256.set64 w (k + 16) hi);
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + 1);
    }
    i <- 0;
    while ((i < 16)) {
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((16 + i) * 8)) /\ ((((16 + i) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, (BArray256.is_init b_w ((16 + i) * 8) 8))]);
      b_s <-
      (BArray128.set64d b_s (i * 8) (W64.of_int 18446744073709551615));
      s <- (BArray128.set64 s i (BArray256.get64 w (16 + i)));
      i <- (i + 1);
    }
    trace_h__H__MUL__XREG____mont_redM <-
    (trace_h__H__MUL__XREG____mont_redM ++
    [(Assert, (BArray128.is_init b_s 0 8))]);
    trace_h__H__MUL__XREG____mont_redM <-
    (trace_h__H__MUL__XREG____mont_redM ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 8) <= 256)))]);
    b_s <- (BArray128.set64d b_s 0 (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <-
    (adc_64 (BArray128.get64 s 0) (BArray256.get64 _P_mP 16) false);
    cf <- aux_5;
    s <- (BArray128.set64 s 0 aux_6);
    i <- 1;
    while ((i < 16)) {
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, (BArray128.is_init b_s (i * 8) 8))]);
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((16 + i) * 8)) /\ ((((16 + i) * 8) + 8) <= 256)))]);
      b_s <-
      (BArray128.set64d b_s (i * 8) (W64.of_int 18446744073709551615));
      (aux_7, aux_8) <-
      (adc_64 (BArray128.get64 s i) (BArray256.get64 _P_mP (16 + i)) cf);
      cf <- aux_7;
      s <- (BArray128.set64 s i aux_8);
      i <- (i + 1);
    }
    ( _8, c) <- (adc_64 c (W64.of_int 0) cf);
    ( _9, cf,  _10,  _11,  _12,  _13) <- (NEG_64 c);
    i <- 0;
    while ((i < 16)) {
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((16 + i) * 8)) /\ ((((16 + i) * 8) + 8) <= 256)))]);
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, (BArray256.is_init b_w ((16 + i) * 8) 8))]);
      x <- (BArray256.get64 w (16 + i));
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, (BArray128.is_init b_s (i * 8) 8))]);
      x <- (cf ? (BArray128.get64 s i) : x);
      trace_h__H__MUL__XREG____mont_redM <-
      (trace_h__H__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 128)))]);
      b_r <-
      (BArray128.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray128.set64 r i x);
      i <- (i + 1);
    }
    return (r, b_r, trace_h__H__MUL__XREG____mont_redM);
  }
  proc h__H__MUL___muln_ (r:BArray256.t, b_r:BArray256.t, a:BArray128.t,
                          b_a:BArray128.t, b:BArray128.t, b_b:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var aux_3:BArray256.t;
    var aux_4:BArray256.t;
    var aux_5:BArray256.t;
    var aux_6:BArray256.t;
    var aux_7:BArray256.t;
    var aux_8:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var b_param_0:BArray256.t;
    var param_2:BArray256.t;
    var param_3:BArray128.t;
    var param_4:BArray128.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var b_param_1:BArray256.t;
    var param_5:BArray256.t;
    var param_6:BArray128.t;
    var param_7:BArray128.t;
    var result_1:BArray256.t;
    var b_result_1:BArray256.t;
    var b_param_2:BArray256.t;
    var param_8:BArray256.t;
    var param_9:BArray128.t;
    var param_10:BArray128.t;
    var result_2:BArray256.t;
    var b_result_2:BArray256.t;
    var b_param_3:BArray256.t;
    var param_11:BArray256.t;
    var param_12:BArray128.t;
    var param_13:BArray128.t;
    var result_3:BArray256.t;
    var b_result_3:BArray256.t;
    var trace_h__H__MUL___muln_:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_9 <- witness;
    param_10 <- witness;
    param_11 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    trace_h__H__MUL___muln_ <- [];
    trace_h__H__MUL___muln_ <-
    (trace_h__H__MUL___muln_ ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    if ((((W256.of_int 0) `&` (W256.of_int 3)) = (W256.of_int 3))) {
      if ((16 <= 0)) {
        b_param <- b_r;
        param <- r;
        param_0 <- a;
        param_1 <- b;
        (aux_7, aux_8, tmp__trace) <@ h__H__MUL__XREG___os_muln_ (param,
        b_param, param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
        (BArray128.init_arr (W8.of_int 255)));
        result <- aux_7;
        b_result <- aux_8;
        trace_h__H__MUL___muln_ <- (trace_h__H__MUL___muln_ ++ tmp__trace);
        trace_h__H__MUL___muln_ <-
        (trace_h__H__MUL___muln_ ++
        [(Assert, (BArray256.is_init b_result 0 256))]);
        r <- result;
      } else {
        if ((16 <= 64)) {
          b_param_0 <- b_r;
          param_2 <- r;
          param_3 <- a;
          param_4 <- b;
          (aux_5, aux_6, tmp__trace) <@ h__H__MUL__XUNR___os_muln_ (param_2,
          b_param_0, param_3, (BArray128.init_arr (W8.of_int 255)), param_4,
          (BArray128.init_arr (W8.of_int 255)));
          result_0 <- aux_5;
          b_result_0 <- aux_6;
          trace_h__H__MUL___muln_ <- (trace_h__H__MUL___muln_ ++ tmp__trace);
          trace_h__H__MUL___muln_ <-
          (trace_h__H__MUL___muln_ ++
          [(Assert, (BArray256.is_init b_result_0 0 256))]);
          r <- result_0;
        } else {
          b_param_1 <- b_r;
          param_5 <- r;
          param_6 <- a;
          param_7 <- b;
          (aux_3, aux_4, tmp__trace) <@ h__H__MUL__XLOOP___os_muln_ (
          param_5, b_param_1, param_6, (BArray128.init_arr (W8.of_int 255)),
          param_7, (BArray128.init_arr (W8.of_int 255)));
          result_1 <- aux_3;
          b_result_1 <- aux_4;
          trace_h__H__MUL___muln_ <- (trace_h__H__MUL___muln_ ++ tmp__trace);
          trace_h__H__MUL___muln_ <-
          (trace_h__H__MUL___muln_ ++
          [(Assert, (BArray256.is_init b_result_1 0 256))]);
          r <- result_1;
        }
      }
    } else {
      if ((16 <= 64)) {
        b_param_2 <- b_r;
        param_8 <- r;
        param_9 <- a;
        param_10 <- b;
        (aux_1, aux_2, tmp__trace) <@ h__H__MUL__UNR___ps_muln_ (param_8,
        b_param_2, param_9, (BArray128.init_arr (W8.of_int 255)), param_10,
        (BArray128.init_arr (W8.of_int 255)));
        result_2 <- aux_1;
        b_result_2 <- aux_2;
        trace_h__H__MUL___muln_ <- (trace_h__H__MUL___muln_ ++ tmp__trace);
        trace_h__H__MUL___muln_ <-
        (trace_h__H__MUL___muln_ ++
        [(Assert, (BArray256.is_init b_result_2 0 256))]);
        r <- result_2;
      } else {
        b_param_3 <- b_r;
        param_11 <- r;
        param_12 <- a;
        param_13 <- b;
        (aux, aux_0, tmp__trace) <@ h__H__MUL__LOOP___os_muln_ (param_11,
        b_param_3, param_12, (BArray128.init_arr (W8.of_int 255)), param_13,
        (BArray128.init_arr (W8.of_int 255)));
        result_3 <- aux;
        b_result_3 <- aux_0;
        trace_h__H__MUL___muln_ <- (trace_h__H__MUL___muln_ ++ tmp__trace);
        trace_h__H__MUL___muln_ <-
        (trace_h__H__MUL___muln_ ++
        [(Assert, (BArray256.is_init b_result_3 0 256))]);
        r <- result_3;
      }
    }
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL___muln_);
  }
  proc h__H__MUL___sqrn_ (r:BArray256.t, b_r:BArray256.t, a:BArray128.t,
                          b_a:BArray128.t) : BArray256.t * BArray256.t *
                                             trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var aux_3:BArray256.t;
    var aux_4:BArray256.t;
    var aux_5:BArray256.t;
    var aux_6:BArray256.t;
    var aux_7:BArray256.t;
    var aux_8:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var b_param_0:BArray256.t;
    var param_1:BArray256.t;
    var param_2:BArray128.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var b_param_1:BArray256.t;
    var param_3:BArray256.t;
    var param_4:BArray128.t;
    var result_1:BArray256.t;
    var b_result_1:BArray256.t;
    var b_param_2:BArray256.t;
    var param_5:BArray256.t;
    var param_6:BArray128.t;
    var result_2:BArray256.t;
    var b_result_2:BArray256.t;
    var b_param_3:BArray256.t;
    var param_7:BArray256.t;
    var param_8:BArray128.t;
    var result_3:BArray256.t;
    var b_result_3:BArray256.t;
    var trace_h__H__MUL___sqrn_:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    trace_h__H__MUL___sqrn_ <- [];
    trace_h__H__MUL___sqrn_ <-
    (trace_h__H__MUL___sqrn_ ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    if ((((W256.of_int 0) `&` (W256.of_int 3)) = (W256.of_int 3))) {
      if ((16 <= 0)) {
        b_param <- b_r;
        param <- r;
        param_0 <- a;
        (aux_7, aux_8, tmp__trace) <@ h__H__MUL__XREG___os_sqrn_ (param,
        b_param, param_0, (BArray128.init_arr (W8.of_int 255)));
        result <- aux_7;
        b_result <- aux_8;
        trace_h__H__MUL___sqrn_ <- (trace_h__H__MUL___sqrn_ ++ tmp__trace);
        trace_h__H__MUL___sqrn_ <-
        (trace_h__H__MUL___sqrn_ ++
        [(Assert, (BArray256.is_init b_result 0 256))]);
        r <- result;
      } else {
        if ((16 <= 64)) {
          b_param_0 <- b_r;
          param_1 <- r;
          param_2 <- a;
          (aux_5, aux_6, tmp__trace) <@ h__H__MUL__XUNR___os_sqrn_ (param_1,
          b_param_0, param_2, (BArray128.init_arr (W8.of_int 255)));
          result_0 <- aux_5;
          b_result_0 <- aux_6;
          trace_h__H__MUL___sqrn_ <- (trace_h__H__MUL___sqrn_ ++ tmp__trace);
          trace_h__H__MUL___sqrn_ <-
          (trace_h__H__MUL___sqrn_ ++
          [(Assert, (BArray256.is_init b_result_0 0 256))]);
          r <- result_0;
        } else {
          b_param_1 <- b_r;
          param_3 <- r;
          param_4 <- a;
          (aux_3, aux_4, tmp__trace) <@ h__H__MUL__XLOOP___os_sqrn_ (
          param_3, b_param_1, param_4, (BArray128.init_arr (W8.of_int 255)));
          result_1 <- aux_3;
          b_result_1 <- aux_4;
          trace_h__H__MUL___sqrn_ <- (trace_h__H__MUL___sqrn_ ++ tmp__trace);
          trace_h__H__MUL___sqrn_ <-
          (trace_h__H__MUL___sqrn_ ++
          [(Assert, (BArray256.is_init b_result_1 0 256))]);
          r <- result_1;
        }
      }
    } else {
      if ((16 <= 64)) {
        b_param_2 <- b_r;
        param_5 <- r;
        param_6 <- a;
        (aux_1, aux_2, tmp__trace) <@ h__H__MUL__UNR___ps_sqrn_ (param_5,
        b_param_2, param_6, (BArray128.init_arr (W8.of_int 255)));
        result_2 <- aux_1;
        b_result_2 <- aux_2;
        trace_h__H__MUL___sqrn_ <- (trace_h__H__MUL___sqrn_ ++ tmp__trace);
        trace_h__H__MUL___sqrn_ <-
        (trace_h__H__MUL___sqrn_ ++
        [(Assert, (BArray256.is_init b_result_2 0 256))]);
        r <- result_2;
      } else {
        b_param_3 <- b_r;
        param_7 <- r;
        param_8 <- a;
        (aux, aux_0, tmp__trace) <@ h__H__MUL__LOOP___os_sqrn_ (param_7,
        b_param_3, param_8, (BArray128.init_arr (W8.of_int 255)));
        result_3 <- aux;
        b_result_3 <- aux_0;
        trace_h__H__MUL___sqrn_ <- (trace_h__H__MUL___sqrn_ ++ tmp__trace);
        trace_h__H__MUL___sqrn_ <-
        (trace_h__H__MUL___sqrn_ ++
        [(Assert, (BArray256.is_init b_result_3 0 256))]);
        r <- result_3;
      }
    }
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL___sqrn_);
  }
  proc h__H__MUL____mont_redM (r:BArray128.t, b_r:BArray128.t, a:BArray256.t,
                               b_a:BArray256.t, _P_mP:BArray256.t,
                               b__P_mP:BArray256.t, _U0:W64.t) : BArray128.t *
                                                                 BArray128.t *
                                                                 trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux_2:BArray128.t;
    var aux_3:BArray128.t;
    var aux_4:BArray128.t;
    var aux_5:BArray128.t;
    var aux_6:BArray128.t;
    var aux_7:BArray128.t;
    var aux_8:BArray128.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var param_2:W64.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var b_param_0:BArray128.t;
    var param_3:BArray128.t;
    var param_4:BArray256.t;
    var param_5:BArray256.t;
    var param_6:W64.t;
    var result_0:BArray128.t;
    var b_result_0:BArray128.t;
    var b_param_1:BArray128.t;
    var param_7:BArray128.t;
    var param_8:BArray256.t;
    var param_9:BArray256.t;
    var param_10:W64.t;
    var result_1:BArray128.t;
    var b_result_1:BArray128.t;
    var b_param_2:BArray128.t;
    var param_11:BArray128.t;
    var param_12:BArray256.t;
    var param_13:BArray256.t;
    var param_14:W64.t;
    var result_2:BArray128.t;
    var b_result_2:BArray128.t;
    var b_param_3:BArray128.t;
    var param_15:BArray128.t;
    var param_16:BArray256.t;
    var param_17:BArray256.t;
    var param_18:W64.t;
    var result_3:BArray128.t;
    var b_result_3:BArray128.t;
    var trace_h__H__MUL____mont_redM:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_9 <- witness;
    param_11 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    param_15 <- witness;
    param_16 <- witness;
    param_17 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    trace_h__H__MUL____mont_redM <- [];
    trace_h__H__MUL____mont_redM <-
    (trace_h__H__MUL____mont_redM ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b__P_mP 0 256)))]);
    if ((((W256.of_int 0) `&` (W256.of_int 3)) = (W256.of_int 3))) {
      if ((16 <= 0)) {
        b_param <- b_r;
        param <- r;
        param_0 <- a;
        param_1 <- _P_mP;
        param_2 <- _U0;
        (aux_7, aux_8, tmp__trace) <@ h__H__MUL__XREG____mont_redM (param,
        b_param, param_0, (BArray256.init_arr (W8.of_int 255)), param_1,
        (BArray256.init_arr (W8.of_int 255)), param_2);
        result <- aux_7;
        b_result <- aux_8;
        trace_h__H__MUL____mont_redM <-
        (trace_h__H__MUL____mont_redM ++ tmp__trace);
        trace_h__H__MUL____mont_redM <-
        (trace_h__H__MUL____mont_redM ++
        [(Assert, (BArray128.is_init b_result 0 128))]);
        r <- result;
      } else {
        if ((16 <= 64)) {
          b_param_0 <- b_r;
          param_3 <- r;
          param_4 <- a;
          param_5 <- _P_mP;
          param_6 <- _U0;
          (aux_5, aux_6, tmp__trace) <@ h__H__MUL__XUNR____mont_redM (
          param_3, b_param_0, param_4, (BArray256.init_arr (W8.of_int 255)),
          param_5, (BArray256.init_arr (W8.of_int 255)), param_6);
          result_0 <- aux_5;
          b_result_0 <- aux_6;
          trace_h__H__MUL____mont_redM <-
          (trace_h__H__MUL____mont_redM ++ tmp__trace);
          trace_h__H__MUL____mont_redM <-
          (trace_h__H__MUL____mont_redM ++
          [(Assert, (BArray128.is_init b_result_0 0 128))]);
          r <- result_0;
        } else {
          b_param_1 <- b_r;
          param_7 <- r;
          param_8 <- a;
          param_9 <- _P_mP;
          param_10 <- _U0;
          (aux_3, aux_4, tmp__trace) <@ h__H__MUL__XLOOP____mont_redM (
          param_7, b_param_1, param_8, (BArray256.init_arr (W8.of_int 255)),
          param_9, (BArray256.init_arr (W8.of_int 255)), param_10);
          result_1 <- aux_3;
          b_result_1 <- aux_4;
          trace_h__H__MUL____mont_redM <-
          (trace_h__H__MUL____mont_redM ++ tmp__trace);
          trace_h__H__MUL____mont_redM <-
          (trace_h__H__MUL____mont_redM ++
          [(Assert, (BArray128.is_init b_result_1 0 128))]);
          r <- result_1;
        }
      }
    } else {
      if ((16 <= 64)) {
        b_param_2 <- b_r;
        param_11 <- r;
        param_12 <- a;
        param_13 <- _P_mP;
        param_14 <- _U0;
        (aux_1, aux_2, tmp__trace) <@ h__H__MUL__UNR____mont_redM (param_11,
        b_param_2, param_12, (BArray256.init_arr (W8.of_int 255)), param_13,
        (BArray256.init_arr (W8.of_int 255)), param_14);
        result_2 <- aux_1;
        b_result_2 <- aux_2;
        trace_h__H__MUL____mont_redM <-
        (trace_h__H__MUL____mont_redM ++ tmp__trace);
        trace_h__H__MUL____mont_redM <-
        (trace_h__H__MUL____mont_redM ++
        [(Assert, (BArray128.is_init b_result_2 0 128))]);
        r <- result_2;
      } else {
        b_param_3 <- b_r;
        param_15 <- r;
        param_16 <- a;
        param_17 <- _P_mP;
        param_18 <- _U0;
        (aux, aux_0, tmp__trace) <@ h__H__MUL__LOOP____mont_redM (param_15,
        b_param_3, param_16, (BArray256.init_arr (W8.of_int 255)), param_17,
        (BArray256.init_arr (W8.of_int 255)), param_18);
        result_3 <- aux;
        b_result_3 <- aux_0;
        trace_h__H__MUL____mont_redM <-
        (trace_h__H__MUL____mont_redM ++ tmp__trace);
        trace_h__H__MUL____mont_redM <-
        (trace_h__H__MUL____mont_redM ++
        [(Assert, (BArray128.is_init b_result_3 0 128))]);
        r <- result_3;
      }
    }
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL____mont_redM);
  }
  proc h__H__FPM__fun_muln (r:BArray256.t, b_r:BArray256.t, a:BArray128.t,
                            b_a:BArray128.t, b:BArray128.t, b_b:BArray128.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__FPM__fun_muln:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__FPM__fun_muln <- [];
    trace_h__H__FPM__fun_muln <-
    (trace_h__H__FPM__fun_muln ++
    [(Assert,
     ((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL___muln_ (param, b_param, param_0,
    (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM__fun_muln <- (trace_h__H__FPM__fun_muln ++ tmp__trace);
    trace_h__H__FPM__fun_muln <-
    (trace_h__H__FPM__fun_muln ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__FPM__fun_muln);
  }
  proc h__H__FPM__fun_sqrn (r:BArray256.t, b_r:BArray256.t, a:BArray128.t,
                            b_a:BArray128.t) : BArray256.t * BArray256.t *
                                               trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__H__FPM__fun_sqrn:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__H__FPM__fun_sqrn <- [];
    trace_h__H__FPM__fun_sqrn <-
    (trace_h__H__FPM__fun_sqrn ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__H__MUL___sqrn_ (param, b_param, param_0,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM__fun_sqrn <- (trace_h__H__FPM__fun_sqrn ++ tmp__trace);
    trace_h__H__FPM__fun_sqrn <-
    (trace_h__H__FPM__fun_sqrn ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__FPM__fun_sqrn);
  }
  proc h__H__FPM___redM (r:BArray128.t, b_r:BArray128.t, a:BArray256.t,
                         b_a:BArray256.t, ctx:BArray520.t, b_ctx:BArray520.t) : 
  BArray128.t * BArray128.t * trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var t:W64.t;
    var _u0:W64.t;
    var b_PmP:BArray256.t;
    var pmP:BArray256.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray256.t;
    var b_param_0:BArray256.t;
    var param_1:BArray256.t;
    var param_2:W64.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__FPM___redM:trace;
    pmP <- witness;
    b_PmP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__FPM___redM <- [];
    trace_h__H__FPM___redM <-
    (trace_h__H__FPM___redM ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray520.is_init b_ctx 0 520)))]);
    trace_h__H__FPM___redM <-
    (trace_h__H__FPM___redM ++
    [(Assert, ((0 <= (64 * 8)) /\ (((64 * 8) + 8) <= 520)))]);
    t <- (BArray520.get64 ctx 64);
    _u0 <- t;
    trace_h__H__FPM___redM <-
    (trace_h__H__FPM___redM ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 256) <= 520)))]);
    b_PmP <- (SBArray520_256.get_sub64 b_ctx 0);
    pmP <- (SBArray520_256.get_sub64 ctx 0);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    b_param_0 <- b_PmP;
    param_1 <- pmP;
    param_2 <- _u0;
    (aux, aux_0, tmp__trace) <@ h__H__MUL____mont_redM (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1, b_param_0,
    param_2);
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM___redM <- (trace_h__H__FPM___redM ++ tmp__trace);
    trace_h__H__FPM___redM <-
    (trace_h__H__FPM___redM ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    r <- result;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__FPM___redM);
  }
  proc h__H__FPM___redM_ (r:BArray128.t, b_r:BArray128.t, a:BArray256.t,
                          b_a:BArray256.t, ctx:BArray520.t, b_ctx:BArray520.t) : 
  BArray128.t * BArray128.t * trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray256.t;
    var param_1:BArray520.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__FPM___redM_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__FPM___redM_ <- [];
    trace_h__H__FPM___redM_ <-
    (trace_h__H__FPM___redM_ ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray520.is_init b_ctx 0 520)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    ctx <- ctx;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__H__FPM___redM (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray520.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM___redM_ <- (trace_h__H__FPM___redM_ ++ tmp__trace);
    trace_h__H__FPM___redM_ <-
    (trace_h__H__FPM___redM_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    r <- result;
    r <- r;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__FPM___redM_);
  }
  proc h__H__FPM___fromM_ (a:BArray128.t, b_a:BArray128.t, ctx:BArray520.t,
                           b_ctx:BArray520.t) : BArray128.t * BArray128.t *
                                                trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux_2:BArray128.t;
    var aux_3:BArray128.t;
    var aux_4:BArray128.t;
    var b__tmp:BArray256.t;
    var b_tmp2:BArray128.t;
    var tmp2:BArray128.t;
    var _tmp:BArray256.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var b_param_0:BArray128.t;
    var param_1:BArray128.t;
    var result_0:BArray128.t;
    var b_result_0:BArray128.t;
    var b_tmp:BArray256.t;
    var tmp:BArray256.t;
    var param_2:BArray128.t;
    var b_param_1:BArray256.t;
    var param_3:BArray256.t;
    var param_4:BArray520.t;
    var result_1:BArray128.t;
    var b_result_1:BArray128.t;
    var trace_h__H__FPM___fromM_:trace;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_tmp <- witness;
    b_tmp2 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    tmp <- witness;
    tmp2 <- witness;
    trace_h__H__FPM___fromM_ <- [];
    trace_h__H__FPM___fromM_ <-
    (trace_h__H__FPM___fromM_ ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__FPM___fromM_ <-
    (trace_h__H__FPM___fromM_ ++ [(Assert, (BArray520.is_init b_ctx 0 520))]);
    b__tmp <- (BArray256.init_arr (W8.of_int 0));
    b_tmp2 <- (SBArray256_128.get_sub64 b__tmp 0);
    tmp2 <- (SBArray256_128.get_sub64 _tmp 0);
    b_param <- b_tmp2;
    param <- tmp2;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__H__BN___mov_ (param, b_param, param_0,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM___fromM_ <- (trace_h__H__FPM___fromM_ ++ tmp__trace);
    trace_h__H__FPM___fromM_ <-
    (trace_h__H__FPM___fromM_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    tmp2 <- result;
    b__tmp <-
    (SBArray256_128.set_sub64 b__tmp 0 (BArray128.init_arr (W8.of_int 255)));
    _tmp <- (SBArray256_128.set_sub64 _tmp 0 tmp2);
    trace_h__H__FPM___fromM_ <-
    (trace_h__H__FPM___fromM_ ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 256)))]);
    b_tmp2 <- (SBArray256_128.get_sub64 b__tmp 16);
    tmp2 <- (SBArray256_128.get_sub64 _tmp 16);
    b_param_0 <- b_tmp2;
    param_1 <- tmp2;
    (aux_1, aux_2, tmp__trace) <@ h__H__BN___set0_ (param_1, b_param_0);
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__H__FPM___fromM_ <- (trace_h__H__FPM___fromM_ ++ tmp__trace);
    trace_h__H__FPM___fromM_ <-
    (trace_h__H__FPM___fromM_ ++
    [(Assert, (BArray128.is_init b_result_0 0 128))]);
    tmp2 <- result_0;
    trace_h__H__FPM___fromM_ <-
    (trace_h__H__FPM___fromM_ ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 256)))]);
    b__tmp <-
    (SBArray256_128.set_sub64 b__tmp 16 (BArray128.init_arr (W8.of_int 255)));
    _tmp <- (SBArray256_128.set_sub64 _tmp 16 tmp2);
    b_tmp <- b__tmp;
    tmp <- _tmp;
    param_2 <- a;
    b_param_1 <- b_tmp;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_3, aux_4, tmp__trace) <@ h__H__FPM___redM_ (param_2,
    (BArray128.init_arr (W8.of_int 255)), param_3, b_param_1, param_4,
    (BArray520.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_h__H__FPM___fromM_ <- (trace_h__H__FPM___fromM_ ++ tmp__trace);
    trace_h__H__FPM___fromM_ <-
    (trace_h__H__FPM___fromM_ ++
    [(Assert, (BArray128.is_init b_result_1 0 128))]);
    a <- result_1;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__FPM___fromM_);
  }
  proc h__H__FPM__fun_red (r:BArray128.t, b_r:BArray128.t, a:BArray256.t,
                           b_a:BArray256.t, ctx:BArray520.t,
                           b_ctx:BArray520.t) : BArray128.t * BArray128.t *
                                                trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray256.t;
    var param_1:BArray520.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__FPM__fun_red:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__FPM__fun_red <- [];
    trace_h__H__FPM__fun_red <-
    (trace_h__H__FPM__fun_red ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray520.is_init b_ctx 0 520)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__H__FPM___redM_ (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray520.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM__fun_red <- (trace_h__H__FPM__fun_red ++ tmp__trace);
    trace_h__H__FPM__fun_red <-
    (trace_h__H__FPM__fun_red ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    r <- result;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__FPM__fun_red);
  }
  proc h__H__FPM___addm_ (r:BArray128.t, b_r:BArray128.t, a:BArray128.t,
                          b_a:BArray128.t, b:BArray128.t, b_b:BArray128.t,
                          ctx:BArray520.t, b_ctx:BArray520.t) : BArray128.t *
                                                                BArray128.t *
                                                                trace = {
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux_2:BArray128.t;
    var aux_3:BArray128.t;
    var aux:bool;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var result:bool;
    var result_0:BArray128.t;
    var b_result:BArray128.t;
    var cf:bool;
    var lastbit:W64.t;
    var b_tmp:BArray128.t;
    var tmp:BArray128.t;
    var param_2:BArray128.t;
    var b_param_0:BArray128.t;
    var param_3:BArray128.t;
    var param_4:W64.t;
    var result_1:BArray128.t;
    var b_result_0:BArray128.t;
    var  _0:bool;
    var trace_h__H__FPM___addm_:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    result_0 <- witness;
    result_1 <- witness;
    tmp <- witness;
    trace_h__H__FPM___addm_ <- [];
    trace_h__H__FPM___addm_ <-
    (trace_h__H__FPM___addm_ ++
    [(Assert,
     (((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)) /\
     (BArray520.is_init b_ctx 128 128)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___add_ (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__FPM___addm_ <- (trace_h__H__FPM___addm_ ++ tmp__trace);
    trace_h__H__FPM___addm_ <-
    (trace_h__H__FPM___addm_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    cf <- result;
    r <- result_0;
    lastbit <- (W64.of_int 0);
    ( _0, lastbit) <- (adc_64 lastbit (W64.of_int 0) cf);
    trace_h__H__FPM___addm_ <-
    (trace_h__H__FPM___addm_ ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 520)))]);
    b_tmp <- (SBArray520_128.get_sub64 b_ctx 16);
    tmp <- (SBArray520_128.get_sub64 ctx 16);
    param_2 <- r;
    b_param_0 <- b_tmp;
    param_3 <- tmp;
    param_4 <- lastbit;
    (aux_2, aux_3, tmp__trace) <@ h__H__BN___cminusP_ (param_2,
    (BArray128.init_arr (W8.of_int 255)), param_3, b_param_0, param_4);
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__H__FPM___addm_ <- (trace_h__H__FPM___addm_ ++ tmp__trace);
    trace_h__H__FPM___addm_ <-
    (trace_h__H__FPM___addm_ ++
    [(Assert, (BArray128.is_init b_result_0 0 128))]);
    r <- result_1;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__FPM___addm_);
  }
  proc h__H__FPM___submU_ (a:BArray128.t, b_a:BArray128.t, b:BArray128.t,
                           b_b:BArray128.t, ctx:BArray520.t,
                           b_ctx:BArray520.t) : BArray128.t * BArray128.t *
                                                trace = {
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux_2:BArray128.t;
    var aux_3:BArray128.t;
    var aux:bool;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var result:bool;
    var result_0:BArray128.t;
    var b_result:BArray128.t;
    var cf:bool;
    var b_tmp:BArray128.t;
    var tmp:BArray128.t;
    var param_1:BArray128.t;
    var param_2:bool;
    var b_param:BArray128.t;
    var param_3:BArray128.t;
    var result_1:BArray128.t;
    var b_result_0:BArray128.t;
    var trace_h__H__FPM___submU_:trace;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_3 <- witness;
    result_0 <- witness;
    result_1 <- witness;
    tmp <- witness;
    trace_h__H__FPM___submU_ <- [];
    trace_h__H__FPM___submU_ <-
    (trace_h__H__FPM___submU_ ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__FPM___submU_ <-
    (trace_h__H__FPM___submU_ ++ [(Assert, (BArray128.is_init b_b 0 128))]);
    trace_h__H__FPM___submU_ <-
    (trace_h__H__FPM___submU_ ++ [(Assert, (BArray520.is_init b_ctx 0 520))]);
    param <- a;
    param_0 <- b;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___subU_ (param,
    (BArray128.init_arr (W8.of_int 255)), param_0,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__FPM___submU_ <- (trace_h__H__FPM___submU_ ++ tmp__trace);
    trace_h__H__FPM___submU_ <-
    (trace_h__H__FPM___submU_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    cf <- result;
    a <- result_0;
    trace_h__H__FPM___submU_ <-
    (trace_h__H__FPM___submU_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 128) <= 520)))]);
    b_tmp <- (SBArray520_128.get_sub64 b_ctx 0);
    tmp <- (SBArray520_128.get_sub64 ctx 0);
    param_1 <- a;
    param_2 <- cf;
    b_param <- b_tmp;
    param_3 <- tmp;
    (aux_2, aux_3, tmp__trace) <@ h__H__BN___caddU_ (param_1,
    (BArray128.init_arr (W8.of_int 255)), param_2, param_3, b_param);
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__H__FPM___submU_ <- (trace_h__H__FPM___submU_ ++ tmp__trace);
    trace_h__H__FPM___submU_ <-
    (trace_h__H__FPM___submU_ ++
    [(Assert, (BArray128.is_init b_result_0 0 128))]);
    a <- result_1;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__FPM___submU_);
  }
  proc h__H__FPM___mulmU_ (a:BArray128.t, b_a:BArray128.t, b:BArray128.t,
                           b_b:BArray128.t, ctx:BArray520.t,
                           b_ctx:BArray520.t) : BArray128.t * BArray128.t *
                                                trace = {
    var aux_1:BArray128.t;
    var aux_2:BArray128.t;
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b__tmp:BArray256.t;
    var _a:BArray128.t;
    var _ctx:BArray520.t;
    var b_tmp:BArray256.t;
    var tmp:BArray256.t;
    var _tmp:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var param_2:BArray128.t;
    var param_3:BArray256.t;
    var param_4:BArray520.t;
    var result_0:BArray128.t;
    var b_result_0:BArray128.t;
    var trace_h__H__FPM___mulmU_:trace;
    _a <- witness;
    _ctx <- witness;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    tmp <- witness;
    trace_h__H__FPM___mulmU_ <- [];
    trace_h__H__FPM___mulmU_ <-
    (trace_h__H__FPM___mulmU_ ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__FPM___mulmU_ <-
    (trace_h__H__FPM___mulmU_ ++ [(Assert, (BArray128.is_init b_b 0 128))]);
    trace_h__H__FPM___mulmU_ <-
    (trace_h__H__FPM___mulmU_ ++ [(Assert, (BArray520.is_init b_ctx 0 520))]);
    b__tmp <- (BArray256.init_arr (W8.of_int 0));
    _a <- a;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__FPM__fun_muln (param, b_param, 
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM___mulmU_ <- (trace_h__H__FPM___mulmU_ ++ tmp__trace);
    trace_h__H__FPM___mulmU_ <-
    (trace_h__H__FPM___mulmU_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    tmp <- result;
    a <- _a;
    ctx <- _ctx;
    param_2 <- a;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__H__FPM__fun_red (param_2,
    (BArray128.init_arr (W8.of_int 255)), param_3,
    (BArray256.init_arr (W8.of_int 255)), param_4,
    (BArray520.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__H__FPM___mulmU_ <- (trace_h__H__FPM___mulmU_ ++ tmp__trace);
    trace_h__H__FPM___mulmU_ <-
    (trace_h__H__FPM___mulmU_ ++
    [(Assert, (BArray128.is_init b_result_0 0 128))]);
    a <- result_0;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__FPM___mulmU_);
  }
  proc h__H__FPM___sqrmU_ (a:BArray128.t, b_a:BArray128.t, ctx:BArray520.t,
                           b_ctx:BArray520.t) : BArray128.t * BArray128.t *
                                                trace = {
    var aux_1:BArray128.t;
    var aux_2:BArray128.t;
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b__tmp:BArray256.t;
    var _a:BArray128.t;
    var _ctx:BArray520.t;
    var b_tmp:BArray256.t;
    var tmp:BArray256.t;
    var _tmp:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray128.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var param_1:BArray128.t;
    var param_2:BArray256.t;
    var param_3:BArray520.t;
    var result_0:BArray128.t;
    var b_result_0:BArray128.t;
    var trace_h__H__FPM___sqrmU_:trace;
    _a <- witness;
    _ctx <- witness;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    result <- witness;
    result_0 <- witness;
    tmp <- witness;
    trace_h__H__FPM___sqrmU_ <- [];
    trace_h__H__FPM___sqrmU_ <-
    (trace_h__H__FPM___sqrmU_ ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__FPM___sqrmU_ <-
    (trace_h__H__FPM___sqrmU_ ++ [(Assert, (BArray520.is_init b_ctx 0 520))]);
    b__tmp <- (BArray256.init_arr (W8.of_int 0));
    _a <- a;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__H__FPM__fun_sqrn (param, b_param, 
    param_0, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM___sqrmU_ <- (trace_h__H__FPM___sqrmU_ ++ tmp__trace);
    trace_h__H__FPM___sqrmU_ <-
    (trace_h__H__FPM___sqrmU_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    tmp <- result;
    a <- _a;
    ctx <- _ctx;
    param_1 <- a;
    param_2 <- tmp;
    param_3 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__H__FPM__fun_red (param_1,
    (BArray128.init_arr (W8.of_int 255)), param_2,
    (BArray256.init_arr (W8.of_int 255)), param_3,
    (BArray520.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__H__FPM___sqrmU_ <- (trace_h__H__FPM___sqrmU_ ++ tmp__trace);
    trace_h__H__FPM___sqrmU_ <-
    (trace_h__H__FPM___sqrmU_ ++
    [(Assert, (BArray128.is_init b_result_0 0 128))]);
    a <- result_0;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__FPM___sqrmU_);
  }
  proc h__H__FPM__fun_mulU (a:BArray128.t, b_a:BArray128.t, b:BArray128.t,
                            b_b:BArray128.t, ctx:BArray520.t,
                            b_ctx:BArray520.t) : BArray128.t * BArray128.t *
                                                 trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:BArray520.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__FPM__fun_mulU:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__FPM__fun_mulU <- [];
    trace_h__H__FPM__fun_mulU <-
    (trace_h__H__FPM__fun_mulU ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__FPM__fun_mulU <-
    (trace_h__H__FPM__fun_mulU ++ [(Assert, (BArray128.is_init b_b 0 128))]);
    trace_h__H__FPM__fun_mulU <-
    (trace_h__H__FPM__fun_mulU ++
    [(Assert, (BArray520.is_init b_ctx 0 520))]);
    param <- a;
    param_0 <- b;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__H__FPM___mulmU_ (param,
    (BArray128.init_arr (W8.of_int 255)), param_0,
    (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray520.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM__fun_mulU <- (trace_h__H__FPM__fun_mulU ++ tmp__trace);
    trace_h__H__FPM__fun_mulU <-
    (trace_h__H__FPM__fun_mulU ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    a <- result;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__FPM__fun_mulU);
  }
  proc h__H__FPM__fun_sqrU (a:BArray128.t, b_a:BArray128.t, ctx:BArray520.t,
                            b_ctx:BArray520.t) : BArray128.t * BArray128.t *
                                                 trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray520.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__FPM__fun_sqrU:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__H__FPM__fun_sqrU <- [];
    trace_h__H__FPM__fun_sqrU <-
    (trace_h__H__FPM__fun_sqrU ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__FPM__fun_sqrU <-
    (trace_h__H__FPM__fun_sqrU ++
    [(Assert, (BArray520.is_init b_ctx 0 520))]);
    param <- a;
    param_0 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__H__FPM___sqrmU_ (param,
    (BArray128.init_arr (W8.of_int 255)), param_0,
    (BArray520.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM__fun_sqrU <- (trace_h__H__FPM__fun_sqrU ++ tmp__trace);
    trace_h__H__FPM__fun_sqrU <-
    (trace_h__H__FPM__fun_sqrU ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    a <- result;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__FPM__fun_sqrU);
  }
  proc h__H__FPM__EXP____tblsel (r:BArray128.t, b_r:BArray128.t,
                                 tbl:BArray2048.t, b_tbl:BArray2048.t,
                                 idx:W64.t) : BArray128.t * BArray128.t *
                                              trace = {
    var k:W64.t;
    var t:W64.t;
    var i:int;
    var zf:bool;
    var trace_h__H__FPM__EXP____tblsel:trace;
    trace_h__H__FPM__EXP____tblsel <- [];
    trace_h__H__FPM__EXP____tblsel <-
    (trace_h__H__FPM__EXP____tblsel ++
    [(Assert, (BArray2048.is_init b_tbl 0 2048))]);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 16))) {
      trace_h__H__FPM__EXP____tblsel <-
      (trace_h__H__FPM__EXP____tblsel ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\
       ((((W64.to_uint k) * 8) + 8) <= 2048)))]);
      t <- (BArray2048.get64 tbl (W64.to_uint k));
      i <- 1;
      while ((i < 16)) {
        zf <- (idx = (W64.of_int i));
        trace_h__H__FPM__EXP____tblsel <-
        (trace_h__H__FPM__EXP____tblsel ++
        [(Assert,
         ((0 <= ((W64.to_uint (k + (W64.of_int (i * 16)))) * 8)) /\
         ((((W64.to_uint (k + (W64.of_int (i * 16)))) * 8) + 8) <= 2048)))]);
        t <-
        (zf ? (BArray2048.get64 tbl (W64.to_uint (k + (W64.of_int (i * 16))))
              ) : t);
        i <- (i + 1);
      }
      trace_h__H__FPM__EXP____tblsel <-
      (trace_h__H__FPM__EXP____tblsel ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 128)))]);
      b_r <-
      (BArray128.set64d b_r ((W64.to_uint k) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray128.set64 r (W64.to_uint k) t);
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__H__FPM__EXP____tblsel);
  }
  proc h__H__FPM__EXP___expmW (r:BArray128.t, b_r:BArray128.t, a:BArray128.t,
                               b_a:BArray128.t, b:BArray128.t,
                               b_b:BArray128.t, ctx:BArray520.t,
                               b_ctx:BArray520.t) : BArray128.t *
                                                    BArray128.t * trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux_2:BArray128.t;
    var aux_3:BArray128.t;
    var aux_4:BArray128.t;
    var aux_5:BArray128.t;
    var aux_6:BArray128.t;
    var aux_7:BArray128.t;
    var aux_8:BArray128.t;
    var aux_9:BArray128.t;
    var aux_10:BArray128.t;
    var aux_11:BArray128.t;
    var aux_12:BArray128.t;
    var aux_13:BArray128.t;
    var aux_14:BArray128.t;
    var b_tbl:BArray2048.t;
    var b_sel:BArray128.t;
    var b__r:BArray128.t;
    var _r:BArray128.t;
    var _a:BArray128.t;
    var _b:BArray128.t;
    var _ctx:BArray520.t;
    var b_one:BArray128.t;
    var one:BArray128.t;
    var b_p:BArray128.t;
    var p:BArray128.t;
    var tbl:BArray2048.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var b_param_0:BArray128.t;
    var param_0:BArray128.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var b_param_1:BArray128.t;
    var param_1:BArray128.t;
    var param_2:BArray128.t;
    var result_0:BArray128.t;
    var b_result_0:BArray128.t;
    var i:int;
    var b_param_2:BArray128.t;
    var param_3:BArray128.t;
    var param_4:BArray128.t;
    var result_1:BArray128.t;
    var b_result_1:BArray128.t;
    var b_q:BArray128.t;
    var q:BArray128.t;
    var b_param_3:BArray128.t;
    var param_5:BArray128.t;
    var b_param_4:BArray128.t;
    var param_6:BArray128.t;
    var param_7:BArray520.t;
    var result_2:BArray128.t;
    var b_result_2:BArray128.t;
    var b_param_5:BArray128.t;
    var param_8:BArray128.t;
    var b_param_6:BArray128.t;
    var param_9:BArray128.t;
    var result_3:BArray128.t;
    var b_result_3:BArray128.t;
    var j:W64.t;
    var _j:W64.t;
    var t:W64.t;
    var _t:W64.t;
    var k:W64.t;
    var _k:W64.t;
    var idx:W64.t;
    var b_psel:BArray128.t;
    var psel:BArray128.t;
    var sel:BArray128.t;
    var b_ptbl:BArray2048.t;
    var ptbl:BArray2048.t;
    var b_param_7:BArray128.t;
    var param_10:BArray128.t;
    var b_param_8:BArray2048.t;
    var param_11:BArray2048.t;
    var param_12:W64.t;
    var result_4:BArray128.t;
    var b_result_4:BArray128.t;
    var s:int;
    var param_13:BArray128.t;
    var param_14:BArray520.t;
    var result_5:BArray128.t;
    var b_result_5:BArray128.t;
    var param_15:BArray128.t;
    var param_16:BArray128.t;
    var param_17:BArray520.t;
    var result_6:BArray128.t;
    var b_result_6:BArray128.t;
    var trace_h__H__FPM__EXP___expmW:trace;
    _a <- witness;
    _b <- witness;
    _ctx <- witness;
    _r <- witness;
    b__r <- witness;
    b_one <- witness;
    b_p <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    b_param_7 <- witness;
    b_param_8 <- witness;
    b_psel <- witness;
    b_ptbl <- witness;
    b_q <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_result_5 <- witness;
    b_result_6 <- witness;
    b_sel <- witness;
    b_tbl <- witness;
    one <- witness;
    p <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_9 <- witness;
    param_10 <- witness;
    param_11 <- witness;
    param_13 <- witness;
    param_14 <- witness;
    param_15 <- witness;
    param_16 <- witness;
    param_17 <- witness;
    psel <- witness;
    ptbl <- witness;
    q <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_4 <- witness;
    result_5 <- witness;
    result_6 <- witness;
    sel <- witness;
    tbl <- witness;
    trace_h__H__FPM__EXP___expmW <- [];
    trace_h__H__FPM__EXP___expmW <-
    (trace_h__H__FPM__EXP___expmW ++
    [(Assert,
     (((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)) /\
     (BArray520.is_init b_ctx 0 520)))]);
    b_tbl <- (BArray2048.init_arr (W8.of_int 0));
    b_sel <- (BArray128.init_arr (W8.of_int 0));
    b__r <- b_r;
    _r <- r;
    _a <- a;
    _b <- b;
    _ctx <- ctx;
    trace_h__H__FPM__EXP___expmW <-
    (trace_h__H__FPM__EXP___expmW ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 128) <= 520)))]);
    b_one <- (SBArray520_128.get_sub64 b_ctx 32);
    one <- (SBArray520_128.get_sub64 ctx 32);
    b_p <- (SBArray2048_128.get_sub64 b_tbl 0);
    p <- (SBArray2048_128.get_sub64 tbl 0);
    b_param <- b_p;
    param <- p;
    b_param_0 <- b_one;
    param_0 <- one;
    (aux, aux_0, tmp__trace) <@ h__H__BN___mov_ (param, b_param, param_0,
    b_param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM__EXP___expmW <-
    (trace_h__H__FPM__EXP___expmW ++ tmp__trace);
    trace_h__H__FPM__EXP___expmW <-
    (trace_h__H__FPM__EXP___expmW ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    p <- result;
    b_tbl <-
    (SBArray2048_128.set_sub64 b_tbl 0 (BArray128.init_arr (W8.of_int 255)));
    tbl <- (SBArray2048_128.set_sub64 tbl 0 p);
    a <- _a;
    trace_h__H__FPM__EXP___expmW <-
    (trace_h__H__FPM__EXP___expmW ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 2048)))]);
    b_p <- (SBArray2048_128.get_sub64 b_tbl 16);
    p <- (SBArray2048_128.get_sub64 tbl 16);
    b_param_1 <- b_p;
    param_1 <- p;
    param_2 <- a;
    (aux_1, aux_2, tmp__trace) <@ h__H__BN___mov_ (param_1, b_param_1,
    param_2, (BArray128.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__H__FPM__EXP___expmW <-
    (trace_h__H__FPM__EXP___expmW ++ tmp__trace);
    trace_h__H__FPM__EXP___expmW <-
    (trace_h__H__FPM__EXP___expmW ++
    [(Assert, (BArray128.is_init b_result_0 0 128))]);
    p <- result_0;
    trace_h__H__FPM__EXP___expmW <-
    (trace_h__H__FPM__EXP___expmW ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 2048)))]);
    b_tbl <-
    (SBArray2048_128.set_sub64 b_tbl 16 (BArray128.init_arr (W8.of_int 255)));
    tbl <- (SBArray2048_128.set_sub64 tbl 16 p);
    i <- 2;
    while ((i < 16)) {
      a <- _a;
      trace_h__H__FPM__EXP___expmW <-
      (trace_h__H__FPM__EXP___expmW ++
      [(Assert, ((0 <= ((i * 16) * 8)) /\ ((((i * 16) * 8) + 128) <= 2048)))]);
      b_p <- (SBArray2048_128.get_sub64 b_tbl (i * 16));
      p <- (SBArray2048_128.get_sub64 tbl (i * 16));
      b_param_2 <- b_p;
      param_3 <- p;
      param_4 <- a;
      (aux_3, aux_4, tmp__trace) <@ h__H__BN___mov_ (param_3, b_param_2,
      param_4, (BArray128.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__H__FPM__EXP___expmW <-
      (trace_h__H__FPM__EXP___expmW ++ tmp__trace);
      trace_h__H__FPM__EXP___expmW <-
      (trace_h__H__FPM__EXP___expmW ++
      [(Assert, (BArray128.is_init b_result_1 0 128))]);
      p <- result_1;
      trace_h__H__FPM__EXP___expmW <-
      (trace_h__H__FPM__EXP___expmW ++
      [(Assert, ((0 <= ((i * 16) * 8)) /\ ((((i * 16) * 8) + 128) <= 2048)))]);
      b_tbl <-
      (SBArray2048_128.set_sub64 b_tbl (i * 16)
      (BArray128.init_arr (W8.of_int 255)));
      tbl <- (SBArray2048_128.set_sub64 tbl (i * 16) p);
      trace_h__H__FPM__EXP___expmW <-
      (trace_h__H__FPM__EXP___expmW ++
      [(Assert,
       ((0 <= (((i - 1) * 16) * 8)) /\
       (((((i - 1) * 16) * 8) + 128) <= 2048)))]);
      b_q <- (SBArray2048_128.get_sub64 b_tbl ((i - 1) * 16));
      q <- (SBArray2048_128.get_sub64 tbl ((i - 1) * 16));
      trace_h__H__FPM__EXP___expmW <-
      (trace_h__H__FPM__EXP___expmW ++
      [(Assert, ((0 <= ((i * 16) * 8)) /\ ((((i * 16) * 8) + 128) <= 2048)))]);
      b_p <- (SBArray2048_128.get_sub64 b_tbl (i * 16));
      p <- (SBArray2048_128.get_sub64 tbl (i * 16));
      ctx <- _ctx;
      b_param_3 <- b_p;
      param_5 <- p;
      b_param_4 <- b_q;
      param_6 <- q;
      param_7 <- ctx;
      (aux_5, aux_6, tmp__trace) <@ h__H__FPM__fun_mulU (param_5, b_param_3,
      param_6, b_param_4, param_7, (BArray520.init_arr (W8.of_int 255)));
      result_2 <- aux_5;
      b_result_2 <- aux_6;
      trace_h__H__FPM__EXP___expmW <-
      (trace_h__H__FPM__EXP___expmW ++ tmp__trace);
      trace_h__H__FPM__EXP___expmW <-
      (trace_h__H__FPM__EXP___expmW ++
      [(Assert, (BArray128.is_init b_result_2 0 128))]);
      p <- result_2;
      trace_h__H__FPM__EXP___expmW <-
      (trace_h__H__FPM__EXP___expmW ++
      [(Assert, ((0 <= ((i * 16) * 8)) /\ ((((i * 16) * 8) + 128) <= 2048)))]);
      b_tbl <-
      (SBArray2048_128.set_sub64 b_tbl (i * 16)
      (BArray128.init_arr (W8.of_int 255)));
      tbl <- (SBArray2048_128.set_sub64 tbl (i * 16) p);
      i <- (i + 1);
    }
    b_r <- b__r;
    r <- _r;
    b_ctx <- (BArray520.init_arr (W8.of_int 255));
    ctx <- _ctx;
    trace_h__H__FPM__EXP___expmW <-
    (trace_h__H__FPM__EXP___expmW ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 128) <= 520)))]);
    b_one <- (SBArray520_128.get_sub64 b_ctx 32);
    one <- (SBArray520_128.get_sub64 ctx 32);
    b_param_5 <- b_r;
    param_8 <- r;
    b_param_6 <- b_one;
    param_9 <- one;
    (aux_7, aux_8, tmp__trace) <@ h__H__BN___mov_ (param_8, b_param_5,
    param_9, b_param_6);
    result_3 <- aux_7;
    b_result_3 <- aux_8;
    trace_h__H__FPM__EXP___expmW <-
    (trace_h__H__FPM__EXP___expmW ++ tmp__trace);
    trace_h__H__FPM__EXP___expmW <-
    (trace_h__H__FPM__EXP___expmW ++
    [(Assert, (BArray128.is_init b_result_3 0 128))]);
    r <- result_3;
    j <- (W64.of_int 16);
    while ((j <> (W64.of_int 0))) {
      j <- (j - (W64.of_int 1));
      _j <- j;
      b <- _b;
      trace_h__H__FPM__EXP___expmW <-
      (trace_h__H__FPM__EXP___expmW ++
      [(Assert,
       ((0 <= ((W64.to_uint j) * 8)) /\ ((((W64.to_uint j) * 8) + 8) <= 128)))]);
      t <- (BArray128.get64 b (W64.to_uint j));
      _t <- t;
      k <- (W64.of_int 16);
      while ((k <> (W64.of_int 0))) {
        _k <- k;
        t <- _t;
        idx <- t;
        idx <- (idx `>>` (W8.of_int 60));
        t <- (t `<<` (W8.of_int 4));
        _t <- t;
        b_psel <- b_sel;
        psel <- sel;
        b_ptbl <- b_tbl;
        ptbl <- tbl;
        b_param_7 <- b_psel;
        param_10 <- psel;
        b_param_8 <- b_ptbl;
        param_11 <- ptbl;
        param_12 <- idx;
        (aux_9, aux_10, tmp__trace) <@ h__H__FPM__EXP____tblsel (param_10,
        b_param_7, param_11, b_param_8, param_12);
        result_4 <- aux_9;
        b_result_4 <- aux_10;
        trace_h__H__FPM__EXP___expmW <-
        (trace_h__H__FPM__EXP___expmW ++ tmp__trace);
        trace_h__H__FPM__EXP___expmW <-
        (trace_h__H__FPM__EXP___expmW ++
        [(Assert, (BArray128.is_init b_result_4 0 128))]);
        psel <- result_4;
        b_sel <- (BArray128.init_arr (W8.of_int 255));
        sel <- psel;
        s <- 0;
        while ((s < 4)) {
          ctx <- _ctx;
          param_13 <- r;
          param_14 <- ctx;
          (aux_11, aux_12, tmp__trace) <@ h__H__FPM__fun_sqrU (param_13,
          (BArray128.init_arr (W8.of_int 255)), param_14,
          (BArray520.init_arr (W8.of_int 255)));
          result_5 <- aux_11;
          b_result_5 <- aux_12;
          trace_h__H__FPM__EXP___expmW <-
          (trace_h__H__FPM__EXP___expmW ++ tmp__trace);
          trace_h__H__FPM__EXP___expmW <-
          (trace_h__H__FPM__EXP___expmW ++
          [(Assert, (BArray128.is_init b_result_5 0 128))]);
          r <- result_5;
          s <- (s + 1);
        }
        psel <- sel;
        ctx <- _ctx;
        param_15 <- r;
        param_16 <- psel;
        param_17 <- ctx;
        (aux_13, aux_14, tmp__trace) <@ h__H__FPM__fun_mulU (param_15,
        (BArray128.init_arr (W8.of_int 255)), param_16,
        (BArray128.init_arr (W8.of_int 255)), param_17,
        (BArray520.init_arr (W8.of_int 255)));
        result_6 <- aux_13;
        b_result_6 <- aux_14;
        trace_h__H__FPM__EXP___expmW <-
        (trace_h__H__FPM__EXP___expmW ++ tmp__trace);
        trace_h__H__FPM__EXP___expmW <-
        (trace_h__H__FPM__EXP___expmW ++
        [(Assert, (BArray128.is_init b_result_6 0 128))]);
        r <- result_6;
        k <- _k;
        k <- (k - (W64.of_int 1));
      }
      j <- _j;
    }
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__FPM__EXP___expmW);
  }
  proc h__H__FPM__EXP___expmW_ (r:BArray128.t, b_r:BArray128.t,
                                a:BArray128.t, b_a:BArray128.t,
                                b:BArray128.t, b_b:BArray128.t,
                                ctx:BArray520.t, b_ctx:BArray520.t) : 
  BArray128.t * BArray128.t * trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:BArray128.t;
    var param_2:BArray520.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__FPM__EXP___expmW_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    result <- witness;
    trace_h__H__FPM__EXP___expmW_ <- [];
    trace_h__H__FPM__EXP___expmW_ <-
    (trace_h__H__FPM__EXP___expmW_ ++
    [(Assert,
     (((BArray128.is_init b_a 0 128) /\ (BArray128.is_init b_b 0 128)) /\
     (BArray520.is_init b_ctx 0 520)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__H__FPM__EXP___expmW (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)), param_1,
    (BArray128.init_arr (W8.of_int 255)), param_2,
    (BArray520.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM__EXP___expmW_ <-
    (trace_h__H__FPM__EXP___expmW_ ++ tmp__trace);
    trace_h__H__FPM__EXP___expmW_ <-
    (trace_h__H__FPM__EXP___expmW_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    r <- result;
    r <- r;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__FPM__EXP___expmW_);
  }
  proc h__H__FPM___toM_ (a:BArray128.t, b_a:BArray128.t, ctx:BArray520.t,
                         b_ctx:BArray520.t) : BArray128.t * BArray128.t *
                                              trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var b_R2:BArray128.t;
    var r2:BArray128.t;
    var param:BArray128.t;
    var b_param:BArray128.t;
    var param_0:BArray128.t;
    var param_1:BArray520.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var trace_h__H__FPM___toM_:trace;
    r2 <- witness;
    b_R2 <- witness;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__FPM___toM_ <- [];
    trace_h__H__FPM___toM_ <-
    (trace_h__H__FPM___toM_ ++ [(Assert, (BArray128.is_init b_a 0 128))]);
    trace_h__H__FPM___toM_ <-
    (trace_h__H__FPM___toM_ ++ [(Assert, (BArray520.is_init b_ctx 0 520))]);
    trace_h__H__FPM___toM_ <-
    (trace_h__H__FPM___toM_ ++
    [(Assert, ((0 <= (48 * 8)) /\ (((48 * 8) + 128) <= 520)))]);
    b_R2 <- (SBArray520_128.get_sub64 b_ctx 48);
    r2 <- (SBArray520_128.get_sub64 ctx 48);
    param <- a;
    b_param <- b_R2;
    param_0 <- r2;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__H__FPM___mulmU_ (param,
    (BArray128.init_arr (W8.of_int 255)), param_0, b_param, param_1,
    (BArray520.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM___toM_ <- (trace_h__H__FPM___toM_ ++ tmp__trace);
    trace_h__H__FPM___toM_ <-
    (trace_h__H__FPM___toM_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    a <- result;
    a <- a;
    b_a <- (BArray128.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__FPM___toM_);
  }
  proc h__H__FPM___ctx_init_ (ctx:BArray520.t, b_ctx:BArray520.t,
                              p:BArray128.t, b_P:BArray128.t) : BArray520.t *
                                                                BArray520.t *
                                                                trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var aux_2:BArray128.t;
    var aux_3:BArray128.t;
    var aux_4:BArray128.t;
    var aux_5:BArray128.t;
    var aux_6:BArray128.t;
    var aux_7:BArray128.t;
    var aux_8:BArray128.t;
    var aux_9:BArray128.t;
    var aux_10:BArray128.t;
    var aux_11:BArray128.t;
    var aux_12:BArray128.t;
    var aux_13:BArray128.t;
    var aux_14:BArray128.t;
    var aux_15:BArray128.t;
    var aux_16:BArray128.t;
    var aux_17:BArray128.t;
    var aux_1:bool;
    var b__x:BArray128.t;
    var b__y:BArray128.t;
    var b_t:BArray128.t;
    var t:BArray128.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray128.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var b_param_0:BArray128.t;
    var param_1:BArray128.t;
    var param_2:BArray128.t;
    var result_0:bool;
    var result_1:BArray128.t;
    var b_result_0:BArray128.t;
    var p0:W64.t;
    var inv:W64.t;
    var j:int;
    var d:W64.t;
    var u0:W64.t;
    var b_x:BArray128.t;
    var x:BArray128.t;
    var _x:BArray128.t;
    var b_param_1:BArray128.t;
    var param_3:BArray128.t;
    var result_2:BArray128.t;
    var b_result_1:BArray128.t;
    var i:W64.t;
    var _i:W64.t;
    var b_y:BArray128.t;
    var y:BArray128.t;
    var _y:BArray128.t;
    var b_param_2:BArray128.t;
    var param_4:BArray128.t;
    var param_5:BArray128.t;
    var param_6:BArray128.t;
    var b_param_3:BArray520.t;
    var param_7:BArray520.t;
    var result_3:BArray128.t;
    var b_result_2:BArray128.t;
    var param_8:BArray128.t;
    var param_9:BArray128.t;
    var param_10:BArray128.t;
    var b_param_4:BArray520.t;
    var param_11:BArray520.t;
    var result_4:BArray128.t;
    var b_result_3:BArray128.t;
    var b_param_5:BArray128.t;
    var param_12:BArray128.t;
    var param_13:BArray128.t;
    var result_5:BArray128.t;
    var b_result_4:BArray128.t;
    var b_param_6:BArray128.t;
    var param_14:BArray128.t;
    var param_15:BArray128.t;
    var param_16:BArray128.t;
    var b_param_7:BArray520.t;
    var param_17:BArray520.t;
    var result_6:BArray128.t;
    var b_result_5:BArray128.t;
    var param_18:BArray128.t;
    var param_19:BArray128.t;
    var param_20:BArray128.t;
    var b_param_8:BArray520.t;
    var param_21:BArray520.t;
    var result_7:BArray128.t;
    var b_result_6:BArray128.t;
    var b_param_9:BArray128.t;
    var param_22:BArray128.t;
    var param_23:BArray128.t;
    var result_8:BArray128.t;
    var b_result_7:BArray128.t;
    var trace_h__H__FPM___ctx_init_:trace;
    _x <- witness;
    _y <- witness;
    b__x <- witness;
    b__y <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    b_param_7 <- witness;
    b_param_8 <- witness;
    b_param_9 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_result_5 <- witness;
    b_result_6 <- witness;
    b_result_7 <- witness;
    b_t <- witness;
    b_x <- witness;
    b_y <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_9 <- witness;
    param_10 <- witness;
    param_11 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    param_14 <- witness;
    param_15 <- witness;
    param_16 <- witness;
    param_17 <- witness;
    param_18 <- witness;
    param_19 <- witness;
    param_20 <- witness;
    param_21 <- witness;
    param_22 <- witness;
    param_23 <- witness;
    result <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_4 <- witness;
    result_5 <- witness;
    result_6 <- witness;
    result_7 <- witness;
    result_8 <- witness;
    t <- witness;
    x <- witness;
    y <- witness;
    trace_h__H__FPM___ctx_init_ <- [];
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, (BArray128.is_init b_P 0 128))]);
    b__x <- (BArray128.init_arr (W8.of_int 0));
    b__y <- (BArray128.init_arr (W8.of_int 0));
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 128) <= 520)))]);
    b_t <- (SBArray520_128.get_sub64 b_ctx 0);
    t <- (SBArray520_128.get_sub64 ctx 0);
    b_param <- b_t;
    param <- t;
    param_0 <- p;
    (aux, aux_0, tmp__trace) <@ h__H__BN___mov_ (param, b_param, param_0,
    (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++ tmp__trace);
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    t <- result;
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 128) <= 520)))]);
    b_ctx <-
    (SBArray520_128.set_sub64 b_ctx 0 (BArray128.init_arr (W8.of_int 255)));
    ctx <- (SBArray520_128.set_sub64 ctx 0 t);
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 520)))]);
    b_t <- (SBArray520_128.get_sub64 b_ctx 16);
    t <- (SBArray520_128.get_sub64 ctx 16);
    b_param_0 <- b_t;
    param_1 <- t;
    param_2 <- p;
    (aux_1, aux_2, aux_3, tmp__trace) <@ h__H__BN___neg_ (param_1, b_param_0,
    param_2, (BArray128.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++ tmp__trace);
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, (BArray128.is_init b_result_0 0 128))]);
    t <- result_1;
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 520)))]);
    b_ctx <-
    (SBArray520_128.set_sub64 b_ctx 16 (BArray128.init_arr (W8.of_int 255)));
    ctx <- (SBArray520_128.set_sub64 ctx 16 t);
    p0 <- (BArray128.get64 p 0);
    inv <- p0;
    j <- 0;
    while ((j < 5)) {
      d <- p0;
      d <- (d * inv);
      d <- (- d);
      d <- (d + (W64.of_int 2));
      inv <- (inv * d);
      j <- (j + 1);
    }
    u0 <- (- inv);
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, ((0 <= (64 * 8)) /\ (((64 * 8) + 8) <= 520)))]);
    b_ctx <-
    (BArray520.set64d b_ctx (64 * 8) (W64.of_int 18446744073709551615));
    ctx <- (BArray520.set64 ctx 64 u0);
    b_x <- b__x;
    x <- _x;
    b_param_1 <- b_x;
    param_3 <- x;
    (aux_4, aux_5, tmp__trace) <@ h__H__BN___set0_ (param_3, b_param_1);
    result_2 <- aux_4;
    b_result_1 <- aux_5;
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++ tmp__trace);
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, (BArray128.is_init b_result_1 0 128))]);
    x <- result_2;
    x <- (BArray128.set64 x 0 (W64.of_int 1));
    _x <- x;
    i <- (W64.of_int (32 * 16));
    while (((W64.of_int 0) \ult i)) {
      _i <- i;
      x <- _x;
      b_y <- b__y;
      y <- _y;
      b_param_2 <- b_y;
      param_4 <- y;
      param_5 <- x;
      param_6 <- x;
      b_param_3 <- b_ctx;
      param_7 <- ctx;
      (aux_6, aux_7, tmp__trace) <@ h__H__FPM___addm_ (param_4, b_param_2,
      param_5, (BArray128.init_arr (W8.of_int 255)), param_6,
      (BArray128.init_arr (W8.of_int 255)), param_7, b_param_3);
      result_3 <- aux_6;
      b_result_2 <- aux_7;
      trace_h__H__FPM___ctx_init_ <-
      (trace_h__H__FPM___ctx_init_ ++ tmp__trace);
      trace_h__H__FPM___ctx_init_ <-
      (trace_h__H__FPM___ctx_init_ ++
      [(Assert, (BArray128.is_init b_result_2 0 128))]);
      y <- result_3;
      b__y <- (BArray128.init_arr (W8.of_int 255));
      _y <- y;
      x <- _x;
      y <- _y;
      param_8 <- x;
      param_9 <- y;
      param_10 <- y;
      b_param_4 <- b_ctx;
      param_11 <- ctx;
      (aux_8, aux_9, tmp__trace) <@ h__H__FPM___addm_ (param_8,
      (BArray128.init_arr (W8.of_int 255)), param_9,
      (BArray128.init_arr (W8.of_int 255)), param_10,
      (BArray128.init_arr (W8.of_int 255)), param_11, b_param_4);
      result_4 <- aux_8;
      b_result_3 <- aux_9;
      trace_h__H__FPM___ctx_init_ <-
      (trace_h__H__FPM___ctx_init_ ++ tmp__trace);
      trace_h__H__FPM___ctx_init_ <-
      (trace_h__H__FPM___ctx_init_ ++
      [(Assert, (BArray128.is_init b_result_3 0 128))]);
      x <- result_4;
      _x <- x;
      i <- _i;
      i <- (i - (W64.of_int 1));
    }
    x <- _x;
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 128) <= 520)))]);
    b_t <- (SBArray520_128.get_sub64 b_ctx 32);
    t <- (SBArray520_128.get_sub64 ctx 32);
    b_param_5 <- b_t;
    param_12 <- t;
    param_13 <- x;
    (aux_10, aux_11, tmp__trace) <@ h__H__BN___mov_ (param_12, b_param_5,
    param_13, (BArray128.init_arr (W8.of_int 255)));
    result_5 <- aux_10;
    b_result_4 <- aux_11;
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++ tmp__trace);
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, (BArray128.is_init b_result_4 0 128))]);
    t <- result_5;
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 128) <= 520)))]);
    b_ctx <-
    (SBArray520_128.set_sub64 b_ctx 32 (BArray128.init_arr (W8.of_int 255)));
    ctx <- (SBArray520_128.set_sub64 ctx 32 t);
    i <- (W64.of_int (32 * 16));
    while (((W64.of_int 0) \ult i)) {
      _i <- i;
      x <- _x;
      b_y <- b__y;
      y <- _y;
      b_param_6 <- b_y;
      param_14 <- y;
      param_15 <- x;
      param_16 <- x;
      b_param_7 <- b_ctx;
      param_17 <- ctx;
      (aux_12, aux_13, tmp__trace) <@ h__H__FPM___addm_ (param_14, b_param_6,
      param_15, (BArray128.init_arr (W8.of_int 255)), param_16,
      (BArray128.init_arr (W8.of_int 255)), param_17, b_param_7);
      result_6 <- aux_12;
      b_result_5 <- aux_13;
      trace_h__H__FPM___ctx_init_ <-
      (trace_h__H__FPM___ctx_init_ ++ tmp__trace);
      trace_h__H__FPM___ctx_init_ <-
      (trace_h__H__FPM___ctx_init_ ++
      [(Assert, (BArray128.is_init b_result_5 0 128))]);
      y <- result_6;
      b__y <- (BArray128.init_arr (W8.of_int 255));
      _y <- y;
      x <- _x;
      y <- _y;
      param_18 <- x;
      param_19 <- y;
      param_20 <- y;
      b_param_8 <- b_ctx;
      param_21 <- ctx;
      (aux_14, aux_15, tmp__trace) <@ h__H__FPM___addm_ (param_18,
      (BArray128.init_arr (W8.of_int 255)), param_19,
      (BArray128.init_arr (W8.of_int 255)), param_20,
      (BArray128.init_arr (W8.of_int 255)), param_21, b_param_8);
      result_7 <- aux_14;
      b_result_6 <- aux_15;
      trace_h__H__FPM___ctx_init_ <-
      (trace_h__H__FPM___ctx_init_ ++ tmp__trace);
      trace_h__H__FPM___ctx_init_ <-
      (trace_h__H__FPM___ctx_init_ ++
      [(Assert, (BArray128.is_init b_result_6 0 128))]);
      x <- result_7;
      _x <- x;
      i <- _i;
      i <- (i - (W64.of_int 1));
    }
    x <- _x;
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, ((0 <= (48 * 8)) /\ (((48 * 8) + 128) <= 520)))]);
    b_t <- (SBArray520_128.get_sub64 b_ctx 48);
    t <- (SBArray520_128.get_sub64 ctx 48);
    b_param_9 <- b_t;
    param_22 <- t;
    param_23 <- x;
    (aux_16, aux_17, tmp__trace) <@ h__H__BN___mov_ (param_22, b_param_9,
    param_23, (BArray128.init_arr (W8.of_int 255)));
    result_8 <- aux_16;
    b_result_7 <- aux_17;
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++ tmp__trace);
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, (BArray128.is_init b_result_7 0 128))]);
    t <- result_8;
    trace_h__H__FPM___ctx_init_ <-
    (trace_h__H__FPM___ctx_init_ ++
    [(Assert, ((0 <= (48 * 8)) /\ (((48 * 8) + 128) <= 520)))]);
    b_ctx <-
    (SBArray520_128.set_sub64 b_ctx 48 (BArray128.init_arr (W8.of_int 255)));
    ctx <- (SBArray520_128.set_sub64 ctx 48 t);
    return (ctx, b_ctx, trace_h__H__FPM___ctx_init_);
  }
  proc h__BN____mov (r:BArray256.t, b_r:BArray256.t, a:BArray256.t,
                     b_a:BArray256.t) : BArray256.t * BArray256.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____mov:trace;
    trace_h__BN____mov <- [];
    trace_h__BN____mov <-
    (trace_h__BN____mov ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    i <- 0;
    while ((i < 32)) {
      trace_h__BN____mov <-
      (trace_h__BN____mov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      t <- (BArray256.get64 a i);
      trace_h__BN____mov <-
      (trace_h__BN____mov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r i t);
      i <- (i + 1);
    }
    return (r, b_r, trace_h__BN____mov);
  }
  proc h__BN___mov (r:BArray256.t, b_r:BArray256.t, a:BArray256.t,
                    b_a:BArray256.t) : BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___mov:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__BN___mov <- [];
    trace_h__BN___mov <-
    (trace_h__BN___mov ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN____mov (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___mov <- (trace_h__BN___mov ++ tmp__trace);
    trace_h__BN___mov <-
    (trace_h__BN___mov ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__BN___mov);
  }
  proc h__BN___mov_ (r:BArray256.t, b_r:BArray256.t, a:BArray256.t,
                     b_a:BArray256.t) : BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___mov_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__BN___mov_ <- [];
    trace_h__BN___mov_ <-
    (trace_h__BN___mov_ ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN___mov (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___mov_ <- (trace_h__BN___mov_ ++ tmp__trace);
    trace_h__BN___mov_ <-
    (trace_h__BN___mov_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__BN___mov_);
  }
  proc h__BN____cmov (a:BArray256.t, b_a:BArray256.t, cond:bool,
                      b:BArray256.t, b_b:BArray256.t) : BArray256.t *
                                                        BArray256.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____cmov:trace;
    trace_h__BN____cmov <- [];
    trace_h__BN____cmov <-
    (trace_h__BN____cmov ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    trace_h__BN____cmov <-
    (trace_h__BN____cmov ++ [(Assert, (BArray256.is_init b_b 0 256))]);
    i <- 0;
    while ((i < 32)) {
      trace_h__BN____cmov <-
      (trace_h__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      t <- (BArray256.get64 a i);
      trace_h__BN____cmov <-
      (trace_h__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      t <- (cond ? (BArray256.get64 b i) : t);
      trace_h__BN____cmov <-
      (trace_h__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      a <- (BArray256.set64 a i t);
      i <- (i + 1);
    }
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN____cmov);
  }
  proc h__BN___cmov (a:BArray256.t, b_a:BArray256.t, cond:bool,
                     b:BArray256.t, b_b:BArray256.t) : BArray256.t *
                                                       BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var param:BArray256.t;
    var param_0:bool;
    var param_1:BArray256.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___cmov:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__BN___cmov <- [];
    trace_h__BN___cmov <-
    (trace_h__BN___cmov ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    trace_h__BN___cmov <-
    (trace_h__BN___cmov ++ [(Assert, (BArray256.is_init b_b 0 256))]);
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__BN____cmov (param,
    (BArray256.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___cmov <- (trace_h__BN___cmov ++ tmp__trace);
    trace_h__BN___cmov <-
    (trace_h__BN___cmov ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    a <- result;
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___cmov);
  }
  proc h__BN___cmov_ (a:BArray256.t, b_a:BArray256.t, cond:bool,
                      b:BArray256.t, b_b:BArray256.t) : BArray256.t *
                                                        BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var param:BArray256.t;
    var param_0:bool;
    var param_1:BArray256.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___cmov_:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__BN___cmov_ <- [];
    trace_h__BN___cmov_ <-
    (trace_h__BN___cmov_ ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    trace_h__BN___cmov_ <-
    (trace_h__BN___cmov_ ++ [(Assert, (BArray256.is_init b_b 0 256))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__BN___cmov (param,
    (BArray256.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___cmov_ <- (trace_h__BN___cmov_ ++ tmp__trace);
    trace_h__BN___cmov_ <-
    (trace_h__BN___cmov_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    a <- result;
    a <- a;
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___cmov_);
  }
  proc h__BN____fill (a:BArray256.t, b_a:BArray256.t, x:W64.t) : BArray256.t *
                                                                 BArray256.t *
                                                                 trace = {
    var i:int;
    var trace_h__BN____fill:trace;
    trace_h__BN____fill <- [];
    i <- 0;
    while ((i < 32)) {
      trace_h__BN____fill <-
      (trace_h__BN____fill ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      b_a <-
      (BArray256.set64d b_a (i * 8) (W64.of_int 18446744073709551615));
      a <- (BArray256.set64 a i x);
      i <- (i + 1);
    }
    return (a, b_a, trace_h__BN____fill);
  }
  proc h__BN___fill_ (a:BArray256.t, b_a:BArray256.t, x:W64.t) : BArray256.t *
                                                                 BArray256.t *
                                                                 trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:W64.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___fill_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___fill_ <- [];
    b_a <- b_a;
    a <- a;
    x <- x;
    b_param <- b_a;
    param <- a;
    param_0 <- x;
    (aux, aux_0, tmp__trace) <@ h__BN____fill (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___fill_ <- (trace_h__BN___fill_ ++ tmp__trace);
    trace_h__BN___fill_ <-
    (trace_h__BN___fill_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    a <- result;
    a <- a;
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___fill_);
  }
  proc h__BN___set0_ (a:BArray256.t, b_a:BArray256.t) : BArray256.t *
                                                        BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var t:W64.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:W64.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___set0_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___set0_ <- [];
    t <- (W64.of_int 0);
    b_param <- b_a;
    param <- a;
    param_0 <- t;
    (aux, aux_0, tmp__trace) <@ h__BN___fill_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___set0_ <- (trace_h__BN___set0_ ++ tmp__trace);
    trace_h__BN___set0_ <-
    (trace_h__BN___set0_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    a <- result;
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___set0_);
  }
  proc h__BN____addc1U (a:BArray256.t, b_a:BArray256.t, b:BArray256.t,
                        b_b:BArray256.t, cf:bool) : bool * BArray256.t *
                                                    BArray256.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var i:int;
    var t:W64.t;
    var trace_h__BN____addc1U:trace;
    trace_h__BN____addc1U <- [];
    trace_h__BN____addc1U <-
    (trace_h__BN____addc1U ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    trace_h__BN____addc1U <-
    (trace_h__BN____addc1U ++ [(Assert, (BArray256.is_init b_b 0 256))]);
    i <- 1;
    while ((i < 32)) {
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      t <- (BArray256.get64 b i);
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      (aux, aux_0) <- (adc_64 (BArray256.get64 a i) t cf);
      cf <- aux;
      a <- (BArray256.set64 a i aux_0);
      i <- (i + 1);
    }
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN____addc1U);
  }
  proc h__BN___addc1U (a:BArray256.t, b_a:BArray256.t, b:BArray256.t,
                       b_b:BArray256.t, cf:bool) : bool * BArray256.t *
                                                   BArray256.t * trace = {
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux:bool;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___addc1U:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1U <- [];
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (BArray256.is_init b_b 0 256))]);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____addc1U (param,
    (BArray256.init_arr (W8.of_int 255)), param_0,
    (BArray256.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1U <- (trace_h__BN___addc1U ++ tmp__trace);
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addc1U);
  }
  proc h__BN___addc1U_ (a:BArray256.t, b_a:BArray256.t, b:BArray256.t,
                        b_b:BArray256.t, cf:bool) : bool * BArray256.t *
                                                    BArray256.t * trace = {
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux:bool;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___addc1U_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1U_ <- [];
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (BArray256.is_init b_b 0 256))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___addc1U (param,
    (BArray256.init_arr (W8.of_int 255)), param_0,
    (BArray256.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1U_ <- (trace_h__BN___addc1U_ ++ tmp__trace);
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    cf <- result;
    a <- result_0;
    a <- a;
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addc1U_);
  }
  proc h__BN___addU_ (a:BArray256.t, b_a:BArray256.t, b:BArray256.t,
                      b_b:BArray256.t) : bool * BArray256.t * BArray256.t *
                                         trace = {
    var aux_2:BArray256.t;
    var aux_3:BArray256.t;
    var aux_0:W64.t;
    var aux:bool;
    var aux_1:bool;
    var t:W64.t;
    var cf:bool;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___addU_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addU_ <- [];
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (BArray256.is_init b_b 0 256))]);
    t <- (BArray256.get64 b 0);
    (aux, aux_0) <- (adc_64 (BArray256.get64 a 0) t false);
    cf <- aux;
    a <- (BArray256.set64 a 0 aux_0);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux_1, aux_2, aux_3, tmp__trace) <@ h__BN___addc1U_ (param,
    (BArray256.init_arr (W8.of_int 255)), param_0,
    (BArray256.init_arr (W8.of_int 255)), param_1);
    result <- aux_1;
    result_0 <- aux_2;
    b_result <- aux_3;
    trace_h__BN___addU_ <- (trace_h__BN___addU_ ++ tmp__trace);
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addU_);
  }
  proc h__BN____addc1 (r:BArray256.t, b_r:BArray256.t, a:BArray256.t,
                       b_a:BArray256.t, b:BArray256.t, b_b:BArray256.t,
                       cf:bool) : bool * BArray256.t * BArray256.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____addc1:trace;
    trace_h__BN____addc1 <- [];
    trace_h__BN____addc1 <-
    (trace_h__BN____addc1 ++
    [(Assert,
     (((BArray256.is_init b_r 0 8) /\ (BArray256.is_init b_a 0 256)) /\
     (BArray256.is_init b_b 0 256)))]);
    i <- 1;
    while ((i < 32)) {
      trace_h__BN____addc1 <-
      (trace_h__BN____addc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      t <- (BArray256.get64 a i);
      trace_h__BN____addc1 <-
      (trace_h__BN____addc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      (cf, t) <- (adc_64 t (BArray256.get64 b i) cf);
      trace_h__BN____addc1 <-
      (trace_h__BN____addc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r i t);
      i <- (i + 1);
    }
    return (cf, r, b_r, trace_h__BN____addc1);
  }
  proc h__BN___addc1 (r:BArray256.t, b_r:BArray256.t, a:BArray256.t,
                      b_a:BArray256.t, b:BArray256.t, b_b:BArray256.t,
                      cf:bool) : bool * BArray256.t * BArray256.t * trace = {
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux:bool;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___addc1:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1 <- [];
    trace_h__BN___addc1 <-
    (trace_h__BN___addc1 ++
    [(Assert,
     (((BArray256.is_init b_r 0 8) /\ (BArray256.is_init b_a 0 256)) /\
     (BArray256.is_init b_b 0 256)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____addc1 (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray256.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1 <- (trace_h__BN___addc1 ++ tmp__trace);
    trace_h__BN___addc1 <-
    (trace_h__BN___addc1 ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___addc1);
  }
  proc h__BN___addc1_ (r:BArray256.t, b_r:BArray256.t, a:BArray256.t,
                       b_a:BArray256.t, b:BArray256.t, b_b:BArray256.t,
                       cf:bool) : bool * BArray256.t * BArray256.t * trace = {
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux:bool;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___addc1_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1_ <- [];
    trace_h__BN___addc1_ <-
    (trace_h__BN___addc1_ ++
    [(Assert,
     (((BArray256.is_init b_r 0 8) /\ (BArray256.is_init b_a 0 256)) /\
     (BArray256.is_init b_b 0 256)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___addc1 (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray256.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1_ <- (trace_h__BN___addc1_ ++ tmp__trace);
    trace_h__BN___addc1_ <-
    (trace_h__BN___addc1_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    cf <- result;
    r <- result_0;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___addc1_);
  }
  proc h__BN___add_ (r:BArray256.t, b_r:BArray256.t, a:BArray256.t,
                     b_a:BArray256.t, b:BArray256.t, b_b:BArray256.t) : 
  bool * BArray256.t * BArray256.t * trace = {
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux:bool;
    var t:W64.t;
    var cf:bool;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___add_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__BN___add_ <- [];
    trace_h__BN___add_ <-
    (trace_h__BN___add_ ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    t <- (BArray256.get64 a 0);
    (cf, t) <- (adc_64 t (BArray256.get64 b 0) false);
    b_r <- (BArray256.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 0 t);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___addc1_ (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray256.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___add_ <- (trace_h__BN___add_ ++ tmp__trace);
    trace_h__BN___add_ <-
    (trace_h__BN___add_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___add_);
  }
  proc h__BN____negc1 (r:BArray256.t, b_r:BArray256.t, a:BArray256.t,
                       b_a:BArray256.t, cf:bool) : bool * BArray256.t *
                                                   BArray256.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____negc1:trace;
    trace_h__BN____negc1 <- [];
    trace_h__BN____negc1 <-
    (trace_h__BN____negc1 ++
    [(Assert, ((BArray256.is_init b_r 0 8) /\ (BArray256.is_init b_a 0 256)))]);
    i <- 1;
    while ((i < 32)) {
      t <- (W64.of_int 0);
      trace_h__BN____negc1 <-
      (trace_h__BN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      (cf, t) <- (sbb_64 t (BArray256.get64 a i) cf);
      trace_h__BN____negc1 <-
      (trace_h__BN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r i t);
      i <- (i + 1);
    }
    return (cf, r, b_r, trace_h__BN____negc1);
  }
  proc h__BN___negc1 (r:BArray256.t, b_r:BArray256.t, a:BArray256.t,
                      b_a:BArray256.t, cf:bool) : bool * BArray256.t *
                                                  BArray256.t * trace = {
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux:bool;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___negc1:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___negc1 <- [];
    trace_h__BN___negc1 <-
    (trace_h__BN___negc1 ++
    [(Assert, ((BArray256.is_init b_r 0 8) /\ (BArray256.is_init b_a 0 256)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____negc1 (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___negc1 <- (trace_h__BN___negc1 ++ tmp__trace);
    trace_h__BN___negc1 <-
    (trace_h__BN___negc1 ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___negc1);
  }
  proc h__BN___negc1_ (r:BArray256.t, b_r:BArray256.t, a:BArray256.t,
                       b_a:BArray256.t, cf:bool) : bool * BArray256.t *
                                                   BArray256.t * trace = {
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux:bool;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___negc1_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___negc1_ <- [];
    trace_h__BN___negc1_ <-
    (trace_h__BN___negc1_ ++
    [(Assert, ((BArray256.is_init b_r 0 8) /\ (BArray256.is_init b_a 0 256)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___negc1 (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___negc1_ <- (trace_h__BN___negc1_ ++ tmp__trace);
    trace_h__BN___negc1_ <-
    (trace_h__BN___negc1_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    cf <- result;
    r <- result_0;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___negc1_);
  }
  proc h__BN___neg_ (r:BArray256.t, b_r:BArray256.t, a:BArray256.t,
                     b_a:BArray256.t) : bool * BArray256.t * BArray256.t *
                                        trace = {
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux:bool;
    var t:W64.t;
    var cf:bool;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__BN___neg_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___neg_ <- [];
    trace_h__BN___neg_ <-
    (trace_h__BN___neg_ ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    t <- (W64.of_int 0);
    (cf, t) <- (sbb_64 t (BArray256.get64 a 0) false);
    b_r <- (BArray256.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray256.set64 r 0 t);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___negc1_ (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___neg_ <- (trace_h__BN___neg_ ++ tmp__trace);
    trace_h__BN___neg_ <-
    (trace_h__BN___neg_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___neg_);
  }
  proc h__BN___cminusP_ (x:BArray256.t, b_x:BArray256.t, mP:BArray256.t,
                         b_mP:BArray256.t, lastbit:W64.t) : BArray256.t *
                                                            BArray256.t *
                                                            trace = {
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var aux_3:BArray256.t;
    var aux:bool;
    var b__tmp:BArray256.t;
    var b_tmp:BArray256.t;
    var tmp:BArray256.t;
    var _tmp:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var result:bool;
    var result_0:BArray256.t;
    var b_result:BArray256.t;
    var _cf:bool;
    var param_2:BArray256.t;
    var param_3:bool;
    var param_4:BArray256.t;
    var result_1:BArray256.t;
    var b_result_0:BArray256.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:W64.t;
    var trace_h__BN___cminusP_:trace;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    result_0 <- witness;
    result_1 <- witness;
    tmp <- witness;
    trace_h__BN___cminusP_ <- [];
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++ [(Assert, (BArray256.is_init b_x 0 256))]);
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++ [(Assert, (BArray256.is_init b_mP 0 256))]);
    b__tmp <- (BArray256.init_arr (W8.of_int 0));
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- x;
    param_1 <- mP;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___add_ (param, b_param, 
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___cminusP_ <- (trace_h__BN___cminusP_ ++ tmp__trace);
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    _cf <- result;
    tmp <- result_0;
    ( _0, lastbit) <- (adc_64 lastbit (W64.of_int 0) _cf);
    ( _1, _cf,  _2,  _3,  _4,  _5) <- (NEG_64 lastbit);
    param_2 <- x;
    param_3 <- _cf;
    param_4 <- tmp;
    (aux_2, aux_3, tmp__trace) <@ h__BN___cmov_ (param_2,
    (BArray256.init_arr (W8.of_int 255)), param_3, param_4,
    (BArray256.init_arr (W8.of_int 255)));
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__BN___cminusP_ <- (trace_h__BN___cminusP_ ++ tmp__trace);
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++
    [(Assert, (BArray256.is_init b_result_0 0 256))]);
    x <- result_1;
    b_x <- (BArray256.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__BN___cminusP_);
  }
  proc h__MUL__UNR____muln_innerloop (x:BArray24.t, b_x:BArray24.t, k:int,
                                      istart:int, iend:int, a:BArray256.t,
                                      b_a:BArray256.t, b:BArray256.t,
                                      b_b:BArray256.t) : BArray24.t *
                                                         BArray24.t * trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var inc:int;
    var i:int;
    var j:int;
    var t0:W64.t;
    var t1:W64.t;
    var param:BArray24.t;
    var param_0:W64.t;
    var param_1:W64.t;
    var param_2:int;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var trace_h__MUL__UNR____muln_innerloop:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__MUL__UNR____muln_innerloop <- [];
    trace_h__MUL__UNR____muln_innerloop <-
    (trace_h__MUL__UNR____muln_innerloop ++
    [(Assert,
     (((((((0 <= istart) /\ (iend <= 32)) /\ (0 <= (k - (iend - 1)))) /\
        ((k - istart) < 32)) /\
       (BArray24.is_init b_x 0 24)) /\
      (BArray256.is_init b_a (8 * istart) (8 * (iend - istart)))) /\
     (BArray256.is_init b_b 0 256)))]);
    inc <- iend;
    i <- istart;
    while ((i < inc)) {
      j <- (k - i);
      trace_h__MUL__UNR____muln_innerloop <-
      (trace_h__MUL__UNR____muln_innerloop ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      trace_h__MUL__UNR____muln_innerloop <-
      (trace_h__MUL__UNR____muln_innerloop ++
      [(Assert, (BArray256.is_init b_a (i * 8) 8))]);
      t0 <- (BArray256.get64 a i);
      trace_h__MUL__UNR____muln_innerloop <-
      (trace_h__MUL__UNR____muln_innerloop ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 256)))]);
      (t1, t0) <- (mulu_64 t0 (BArray256.get64 b j));
      param <- x;
      param_0 <- t1;
      param_1 <- t0;
      param_2 <- k;
      (aux, aux_0, tmp__trace) <@ uTIL____addacc3 (param,
      (BArray24.init_arr (W8.of_int 255)), param_0, param_1, param_2);
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__UNR____muln_innerloop <-
      (trace_h__MUL__UNR____muln_innerloop ++ tmp__trace);
      trace_h__MUL__UNR____muln_innerloop <-
      (trace_h__MUL__UNR____muln_innerloop ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      x <- result;
      i <- (i + 1);
    }
    b_x <- (BArray24.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__MUL__UNR____muln_innerloop);
  }
  proc h__MUL__UNR____ps_muln (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                               b_a:BArray256.t, b:BArray256.t,
                               b_b:BArray256.t) : BArray512.t * BArray512.t *
                                                  trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var aux_1:BArray24.t;
    var aux_2:BArray24.t;
    var inc:int;
    var b_x:BArray24.t;
    var t0:W64.t;
    var t1:W64.t;
    var x:BArray24.t;
    var k:int;
    var b_param:BArray24.t;
    var param:BArray24.t;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var param_3:BArray256.t;
    var param_4:BArray256.t;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var b_param_0:BArray24.t;
    var param_5:BArray24.t;
    var param_6:int;
    var param_7:int;
    var param_8:int;
    var param_9:BArray256.t;
    var param_10:BArray256.t;
    var result_0:BArray24.t;
    var b_result_0:BArray24.t;
    var trace_h__MUL__UNR____ps_muln:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_x <- witness;
    param <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_9 <- witness;
    param_10 <- witness;
    result <- witness;
    result_0 <- witness;
    x <- witness;
    trace_h__MUL__UNR____ps_muln <- [];
    trace_h__MUL__UNR____ps_muln <-
    (trace_h__MUL__UNR____ps_muln ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    b_x <- (BArray24.init_arr (W8.of_int 0));
    t0 <- (BArray256.get64 a 0);
    (t1, t0) <- (mulu_64 t0 (BArray256.get64 b 0));
    b_r <- (BArray512.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 0 t0);
    b_x <- (BArray24.set64d b_x 8 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 1 t1);
    b_x <- (BArray24.set64d b_x 16 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 2 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 0 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 0 (W64.of_int 0));
    k <- 1;
    while ((k < 32)) {
      b_param <- b_x;
      param <- x;
      param_0 <- k;
      param_1 <- 0;
      param_2 <- (k + 1);
      param_3 <- a;
      param_4 <- b;
      (aux, aux_0, tmp__trace) <@ h__MUL__UNR____muln_innerloop (param,
      b_param, param_0, param_1, param_2, param_3,
      (BArray256.init_arr (W8.of_int 255)), param_4,
      (BArray256.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++ tmp__trace);
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result;
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r k t0);
      k <- (k + 1);
    }
    inc <- ((2 * 32) - 1);
    k <- 32;
    while ((k < inc)) {
      b_param_0 <- b_x;
      param_5 <- x;
      param_6 <- k;
      param_7 <- ((k - 32) + 1);
      param_8 <- 32;
      param_9 <- a;
      param_10 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__UNR____muln_innerloop (param_5,
      b_param_0, param_6, param_7, param_8, param_9,
      (BArray256.init_arr (W8.of_int 255)), param_10,
      (BArray256.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++ tmp__trace);
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, (BArray24.is_init b_result_0 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_0;
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r k t0);
      k <- (k + 1);
    }
    trace_h__MUL__UNR____ps_muln <-
    (trace_h__MUL__UNR____ps_muln ++
    [(Assert,
     ((0 <= (((2 * 32) - 1) * 8)) /\ (((((2 * 32) - 1) * 8) + 8) <= 512)))]);
    trace_h__MUL__UNR____ps_muln <-
    (trace_h__MUL__UNR____ps_muln ++
    [(Assert,
     ((0 <= ((((2 * 32) - 1) %% 3) * 8)) /\
     ((((((2 * 32) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____ps_muln <-
    (trace_h__MUL__UNR____ps_muln ++
    [(Assert, (BArray24.is_init b_x ((((2 * 32) - 1) %% 3) * 8) 8))]);
    b_r <-
    (BArray512.set64d b_r (((2 * 32) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <-
    (BArray512.set64 r ((2 * 32) - 1)
    (BArray24.get64 x (((2 * 32) - 1) %% 3)));
    return (r, b_r, trace_h__MUL__UNR____ps_muln);
  }
  proc h__MUL__UNR___ps_muln (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                              b_a:BArray256.t, b:BArray256.t, b_b:BArray256.t) : 
  BArray512.t * BArray512.t * trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__MUL__UNR___ps_muln:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MUL__UNR___ps_muln <- [];
    trace_h__MUL__UNR___ps_muln <-
    (trace_h__MUL__UNR___ps_muln ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__UNR____ps_muln (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__UNR___ps_muln <-
    (trace_h__MUL__UNR___ps_muln ++ tmp__trace);
    trace_h__MUL__UNR___ps_muln <-
    (trace_h__MUL__UNR___ps_muln ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__UNR___ps_muln);
  }
  proc h__MUL__UNR___ps_muln_ (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                               b_a:BArray256.t, b:BArray256.t,
                               b_b:BArray256.t) : BArray512.t * BArray512.t *
                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__MUL__UNR___ps_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MUL__UNR___ps_muln_ <- [];
    trace_h__MUL__UNR___ps_muln_ <-
    (trace_h__MUL__UNR___ps_muln_ ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__UNR___ps_muln (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__UNR___ps_muln_ <-
    (trace_h__MUL__UNR___ps_muln_ ++ tmp__trace);
    trace_h__MUL__UNR___ps_muln_ <-
    (trace_h__MUL__UNR___ps_muln_ ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    r <- r;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__UNR___ps_muln_);
  }
  proc h__MUL__UNR____sqrn_innerloop (x:BArray24.t, b_x:BArray24.t, k:int,
                                      istart:int, iend:int, a:BArray256.t,
                                      b_a:BArray256.t) : BArray24.t *
                                                         BArray24.t * trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var inc:int;
    var i:int;
    var j:int;
    var ti:W64.t;
    var tj:W64.t;
    var param:BArray24.t;
    var param_0:W64.t;
    var param_1:W64.t;
    var param_2:int;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var trace_h__MUL__UNR____sqrn_innerloop:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__MUL__UNR____sqrn_innerloop <- [];
    trace_h__MUL__UNR____sqrn_innerloop <-
    (trace_h__MUL__UNR____sqrn_innerloop ++
    [(Assert,
     ((((((0 <= istart) /\ (iend <= 32)) /\ (0 <= (k - (iend - 1)))) /\
       ((k - istart) < 32)) /\
      (BArray24.is_init b_x 0 24)) /\
     (BArray256.is_init b_a 0 256)))]);
    inc <- iend;
    i <- istart;
    while ((i < inc)) {
      j <- (k - i);
      trace_h__MUL__UNR____sqrn_innerloop <-
      (trace_h__MUL__UNR____sqrn_innerloop ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      ti <- (BArray256.get64 a i);
      trace_h__MUL__UNR____sqrn_innerloop <-
      (trace_h__MUL__UNR____sqrn_innerloop ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 256)))]);
      tj <- (BArray256.get64 a j);
      param <- x;
      param_0 <- ti;
      param_1 <- tj;
      param_2 <- k;
      (aux, aux_0, tmp__trace) <@ uTIL____addacc3x2 (param,
      (BArray24.init_arr (W8.of_int 255)), param_0, param_1, param_2);
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__UNR____sqrn_innerloop <-
      (trace_h__MUL__UNR____sqrn_innerloop ++ tmp__trace);
      trace_h__MUL__UNR____sqrn_innerloop <-
      (trace_h__MUL__UNR____sqrn_innerloop ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      x <- result;
      i <- (i + 1);
    }
    b_x <- (BArray24.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__MUL__UNR____sqrn_innerloop);
  }
  proc h__MUL__UNR____ps_sqrn (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                               b_a:BArray256.t) : BArray512.t * BArray512.t *
                                                  trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var aux_1:BArray24.t;
    var aux_2:BArray24.t;
    var aux_3:BArray24.t;
    var aux_4:BArray24.t;
    var aux_5:BArray24.t;
    var aux_6:BArray24.t;
    var inc:int;
    var b_x:BArray24.t;
    var t0:W64.t;
    var t1:W64.t;
    var x:BArray24.t;
    var k:int;
    var b_param:BArray24.t;
    var param:BArray24.t;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var param_3:BArray256.t;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var param_4:BArray24.t;
    var param_5:W64.t;
    var param_6:W64.t;
    var param_7:int;
    var result_0:BArray24.t;
    var b_result_0:BArray24.t;
    var b_param_0:BArray24.t;
    var param_8:BArray24.t;
    var param_9:int;
    var param_10:int;
    var param_11:int;
    var param_12:BArray256.t;
    var result_1:BArray24.t;
    var b_result_1:BArray24.t;
    var param_13:BArray24.t;
    var param_14:W64.t;
    var param_15:W64.t;
    var param_16:int;
    var result_2:BArray24.t;
    var b_result_2:BArray24.t;
    var trace_h__MUL__UNR____ps_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_x <- witness;
    param <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_8 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    x <- witness;
    trace_h__MUL__UNR____ps_sqrn <- [];
    trace_h__MUL__UNR____ps_sqrn <-
    (trace_h__MUL__UNR____ps_sqrn ++
    [(Assert, (BArray256.is_init b_a 0 256))]);
    b_x <- (BArray24.init_arr (W8.of_int 0));
    t0 <- (BArray256.get64 a 0);
    (t1, t0) <- (mulu_64 t0 t0);
    b_r <- (BArray512.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 0 t0);
    b_x <- (BArray24.set64d b_x 8 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 1 t1);
    b_x <- (BArray24.set64d b_x 16 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 2 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 0 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 0 (W64.of_int 0));
    k <- 1;
    while ((k < 32)) {
      b_param <- b_x;
      param <- x;
      param_0 <- k;
      param_1 <- 0;
      param_2 <- ((k + 1) %/ 2);
      param_3 <- a;
      (aux, aux_0, tmp__trace) <@ h__MUL__UNR____sqrn_innerloop (param,
      b_param, param_0, param_1, param_2, param_3,
      (BArray256.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++ tmp__trace);
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result;
      if (((k %% 2) = 0)) {
        trace_h__MUL__UNR____ps_sqrn <-
        (trace_h__MUL__UNR____ps_sqrn ++
        [(Assert, ((0 <= ((k %/ 2) * 8)) /\ ((((k %/ 2) * 8) + 8) <= 256)))]);
        t0 <- (BArray256.get64 a (k %/ 2));
        (t1, t0) <- (mulu_64 t0 t0);
        param_4 <- x;
        param_5 <- t1;
        param_6 <- t0;
        param_7 <- k;
        (aux_1, aux_2, tmp__trace) <@ uTIL____addacc3 (param_4,
        (BArray24.init_arr (W8.of_int 255)), param_5, param_6, param_7);
        result_0 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__MUL__UNR____ps_sqrn <-
        (trace_h__MUL__UNR____ps_sqrn ++ tmp__trace);
        trace_h__MUL__UNR____ps_sqrn <-
        (trace_h__MUL__UNR____ps_sqrn ++
        [(Assert, (BArray24.is_init b_result_0 0 24))]);
        b_x <- (BArray24.init_arr (W8.of_int 255));
        x <- result_0;
      } else {
        
      }
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r k t0);
      k <- (k + 1);
    }
    inc <- ((2 * 32) - 1);
    k <- 32;
    while ((k < inc)) {
      b_param_0 <- b_x;
      param_8 <- x;
      param_9 <- k;
      param_10 <- ((k - 32) + 1);
      param_11 <- ((k + 1) %/ 2);
      param_12 <- a;
      (aux_3, aux_4, tmp__trace) <@ h__MUL__UNR____sqrn_innerloop (param_8,
      b_param_0, param_9, param_10, param_11, param_12,
      (BArray256.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++ tmp__trace);
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, (BArray24.is_init b_result_1 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_1;
      if (((k %% 2) = 0)) {
        trace_h__MUL__UNR____ps_sqrn <-
        (trace_h__MUL__UNR____ps_sqrn ++
        [(Assert, ((0 <= ((k %/ 2) * 8)) /\ ((((k %/ 2) * 8) + 8) <= 256)))]);
        t0 <- (BArray256.get64 a (k %/ 2));
        (t1, t0) <- (mulu_64 t0 t0);
        param_13 <- x;
        param_14 <- t1;
        param_15 <- t0;
        param_16 <- k;
        (aux_5, aux_6, tmp__trace) <@ uTIL____addacc3 (param_13,
        (BArray24.init_arr (W8.of_int 255)), param_14, param_15, param_16);
        result_2 <- aux_5;
        b_result_2 <- aux_6;
        trace_h__MUL__UNR____ps_sqrn <-
        (trace_h__MUL__UNR____ps_sqrn ++ tmp__trace);
        trace_h__MUL__UNR____ps_sqrn <-
        (trace_h__MUL__UNR____ps_sqrn ++
        [(Assert, (BArray24.is_init b_result_2 0 24))]);
        b_x <- (BArray24.init_arr (W8.of_int 255));
        x <- result_2;
      } else {
        
      }
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r k t0);
      k <- (k + 1);
    }
    trace_h__MUL__UNR____ps_sqrn <-
    (trace_h__MUL__UNR____ps_sqrn ++
    [(Assert,
     ((0 <= (((2 * 32) - 1) * 8)) /\ (((((2 * 32) - 1) * 8) + 8) <= 512)))]);
    trace_h__MUL__UNR____ps_sqrn <-
    (trace_h__MUL__UNR____ps_sqrn ++
    [(Assert,
     ((0 <= ((((2 * 32) - 1) %% 3) * 8)) /\
     ((((((2 * 32) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____ps_sqrn <-
    (trace_h__MUL__UNR____ps_sqrn ++
    [(Assert, (BArray24.is_init b_x ((((2 * 32) - 1) %% 3) * 8) 8))]);
    b_r <-
    (BArray512.set64d b_r (((2 * 32) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <-
    (BArray512.set64 r ((2 * 32) - 1)
    (BArray24.get64 x (((2 * 32) - 1) %% 3)));
    return (r, b_r, trace_h__MUL__UNR____ps_sqrn);
  }
  proc h__MUL__UNR___ps_sqrn (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                              b_a:BArray256.t) : BArray512.t * BArray512.t *
                                                 trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__MUL__UNR___ps_sqrn:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__UNR___ps_sqrn <- [];
    trace_h__MUL__UNR___ps_sqrn <-
    (trace_h__MUL__UNR___ps_sqrn ++
    [(Assert, (BArray256.is_init b_a 0 256))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__UNR____ps_sqrn (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__UNR___ps_sqrn <-
    (trace_h__MUL__UNR___ps_sqrn ++ tmp__trace);
    trace_h__MUL__UNR___ps_sqrn <-
    (trace_h__MUL__UNR___ps_sqrn ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__UNR___ps_sqrn);
  }
  proc h__MUL__UNR___ps_sqrn_ (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                               b_a:BArray256.t) : BArray512.t * BArray512.t *
                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__MUL__UNR___ps_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__UNR___ps_sqrn_ <- [];
    trace_h__MUL__UNR___ps_sqrn_ <-
    (trace_h__MUL__UNR___ps_sqrn_ ++
    [(Assert, (BArray256.is_init b_a 0 256))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__UNR___ps_sqrn (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__UNR___ps_sqrn_ <-
    (trace_h__MUL__UNR___ps_sqrn_ ++ tmp__trace);
    trace_h__MUL__UNR___ps_sqrn_ <-
    (trace_h__MUL__UNR___ps_sqrn_ ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    r <- r;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__UNR___ps_sqrn_);
  }
  proc h__MUL__UNR____mont_redM (r:BArray256.t, b_r:BArray256.t,
                                 a:BArray512.t, b_a:BArray512.t,
                                 _P_mP:BArray512.t, b__P_mP:BArray512.t,
                                 _U0:W64.t) : BArray256.t * BArray256.t *
                                              trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var aux_1:BArray24.t;
    var aux_2:BArray24.t;
    var aux_3:BArray24.t;
    var aux_4:BArray24.t;
    var aux_5:BArray24.t;
    var aux_6:BArray24.t;
    var aux_7:BArray24.t;
    var aux_8:BArray24.t;
    var aux_11:BArray256.t;
    var aux_12:BArray256.t;
    var aux_10:W64.t;
    var aux_9:bool;
    var inc:int;
    var b_x:BArray24.t;
    var x:BArray24.t;
    var b_P:BArray256.t;
    var p:BArray256.t;
    var k:int;
    var b_param:BArray24.t;
    var param:BArray24.t;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var b_param_0:BArray256.t;
    var param_3:BArray256.t;
    var b_param_1:BArray256.t;
    var param_4:BArray256.t;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var zero:W64.t;
    var t0:W64.t;
    var param_5:BArray24.t;
    var param_6:W64.t;
    var param_7:W64.t;
    var param_8:int;
    var result_0:BArray24.t;
    var b_result_0:BArray24.t;
    var t1:W64.t;
    var param_9:BArray24.t;
    var param_10:W64.t;
    var param_11:W64.t;
    var param_12:int;
    var result_1:BArray24.t;
    var b_result_1:BArray24.t;
    var b_param_2:BArray24.t;
    var param_13:BArray24.t;
    var param_14:int;
    var param_15:int;
    var param_16:int;
    var b_param_3:BArray256.t;
    var param_17:BArray256.t;
    var b_param_4:BArray256.t;
    var param_18:BArray256.t;
    var result_2:BArray24.t;
    var b_result_2:BArray24.t;
    var param_19:BArray24.t;
    var param_20:W64.t;
    var param_21:W64.t;
    var param_22:int;
    var result_3:BArray24.t;
    var b_result_3:BArray24.t;
    var lastbit:W64.t;
    var cf:bool;
    var b_mP:BArray256.t;
    var mP:BArray256.t;
    var b_param_5:BArray256.t;
    var param_23:BArray256.t;
    var b_param_6:BArray256.t;
    var param_24:BArray256.t;
    var param_25:W64.t;
    var result_4:BArray256.t;
    var b_result_4:BArray256.t;
    var  _0:W64.t;
    var  _1:bool;
    var trace_h__MUL__UNR____mont_redM:trace;
    p <- witness;
    b_P <- witness;
    b_mP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_x <- witness;
    mP <- witness;
    param <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_9 <- witness;
    param_13 <- witness;
    param_17 <- witness;
    param_18 <- witness;
    param_19 <- witness;
    param_23 <- witness;
    param_24 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_4 <- witness;
    x <- witness;
    trace_h__MUL__UNR____mont_redM <- [];
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((BArray512.is_init b_a 0 512) /\ (BArray512.is_init b__P_mP 0 512)))]);
    b_x <- (BArray24.init_arr (W8.of_int 0));
    b_x <- (BArray24.set64d b_x 0 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 0 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 8 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 1 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 16 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 2 (W64.of_int 0));
    b_P <- (SBArray512_256.get_sub64 b__P_mP 0);
    p <- (SBArray512_256.get_sub64 _P_mP 0);
    k <- 0;
    while ((k < 32)) {
      b_param <- b_x;
      param <- x;
      param_0 <- k;
      param_1 <- 0;
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      b_param_1 <- b_P;
      param_4 <- p;
      (aux, aux_0, tmp__trace) <@ h__MUL__UNR____muln_innerloop (param,
      b_param, param_0, param_1, param_2, param_3, b_param_0, param_4,
      b_param_1);
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      x <- result;
      zero <- (W64.of_int 0);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
      t0 <- (BArray512.get64 a k);
      param_5 <- x;
      param_6 <- zero;
      param_7 <- t0;
      param_8 <- k;
      (aux_1, aux_2, tmp__trace) <@ uTIL____addacc3 (param_5,
      (BArray24.init_arr (W8.of_int 255)), param_6, param_7, param_8);
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result_0 0 24))]);
      x <- result_0;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      ( _0, t0) <- (mulu_64 t0 _U0);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r k t0);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, (BArray256.is_init b_P 0 8))]);
      (t1, t0) <- (mulu_64 t0 (BArray256.get64 p 0));
      param_9 <- x;
      param_10 <- t1;
      param_11 <- t0;
      param_12 <- k;
      (aux_3, aux_4, tmp__trace) <@ uTIL____addacc3 (param_9,
      (BArray24.init_arr (W8.of_int 255)), param_10, param_11, param_12);
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result_1 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_1;
      k <- (k + 1);
    }
    inc <- ((2 * 32) - 1);
    k <- 32;
    while ((k < inc)) {
      b_param_2 <- b_x;
      param_13 <- x;
      param_14 <- k;
      param_15 <- ((k - 32) + 1);
      param_16 <- 32;
      b_param_3 <- b_r;
      param_17 <- r;
      b_param_4 <- b_P;
      param_18 <- p;
      (aux_5, aux_6, tmp__trace) <@ h__MUL__UNR____muln_innerloop (param_13,
      b_param_2, param_14, param_15, param_16, param_17, b_param_3, param_18,
      b_param_4);
      result_2 <- aux_5;
      b_result_2 <- aux_6;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result_2 0 24))]);
      x <- result_2;
      zero <- (W64.of_int 0);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
      t0 <- (BArray512.get64 a k);
      param_19 <- x;
      param_20 <- zero;
      param_21 <- t0;
      param_22 <- k;
      (aux_7, aux_8, tmp__trace) <@ uTIL____addacc3 (param_19,
      (BArray24.init_arr (W8.of_int 255)), param_20, param_21, param_22);
      result_3 <- aux_7;
      b_result_3 <- aux_8;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result_3 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_3;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= ((k - 32) * 8)) /\ ((((k - 32) * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r ((k - 32) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r (k - 32) t0);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      k <- (k + 1);
    }
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= (((2 * 32) %% 3) * 8)) /\ (((((2 * 32) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, (BArray24.is_init b_x (((2 * 32) %% 3) * 8) 8))]);
    lastbit <- (BArray24.get64 x ((2 * 32) %% 3));
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= ((((2 * 32) - 1) %% 3) * 8)) /\
     ((((((2 * 32) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= ((((2 * 32) - 1) %% 3) * 8)) /\
     ((((((2 * 32) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, (BArray24.is_init b_x ((((2 * 32) - 1) %% 3) * 8) 8))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= (((2 * 32) - 1) * 8)) /\ (((((2 * 32) - 1) * 8) + 8) <= 512)))]);
    b_x <-
    (BArray24.set64d b_x ((((2 * 32) - 1) %% 3) * 8)
    (W64.of_int 18446744073709551615));
    (aux_9, aux_10) <-
    (adc_64 (BArray24.get64 x (((2 * 32) - 1) %% 3))
    (BArray512.get64 a ((2 * 32) - 1)) false);
    cf <- aux_9;
    x <- (BArray24.set64 x (((2 * 32) - 1) %% 3) aux_10);
    ( _1, lastbit) <- (adc_64 lastbit (W64.of_int 0) cf);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, ((0 <= ((32 - 1) * 8)) /\ ((((32 - 1) * 8) + 8) <= 256)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= ((((2 * 32) - 1) %% 3) * 8)) /\
     ((((((2 * 32) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, (BArray24.is_init b_x ((((2 * 32) - 1) %% 3) * 8) 8))]);
    b_r <-
    (BArray256.set64d b_r ((32 - 1) * 8) (W64.of_int 18446744073709551615));
    r <-
    (BArray256.set64 r (32 - 1) (BArray24.get64 x (((2 * 32) - 1) %% 3)));
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 256) <= 512)))]);
    b_mP <- (SBArray512_256.get_sub64 b__P_mP 32);
    mP <- (SBArray512_256.get_sub64 _P_mP 32);
    b_param_5 <- b_r;
    param_23 <- r;
    b_param_6 <- b_mP;
    param_24 <- mP;
    param_25 <- lastbit;
    (aux_11, aux_12, tmp__trace) <@ h__BN___cminusP_ (param_23, b_param_5,
    param_24, b_param_6, param_25);
    result_4 <- aux_11;
    b_result_4 <- aux_12;
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++ tmp__trace);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, (BArray256.is_init b_result_4 0 256))]);
    r <- result_4;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__UNR____mont_redM);
  }
  proc h__MUL__LOOP____mul1 (r:BArray512.t, b_r:BArray512.t, a:W64.t,
                             b:BArray256.t, b_b:BArray256.t) : BArray512.t *
                                                               BArray512.t *
                                                               trace = {
    var lo:W64.t;
    var hi:W64.t;
    var c:W64.t;
    var i:int;
    var cf:bool;
    var  _0:bool;
    var trace_h__MUL__LOOP____mul1:trace;
    trace_h__MUL__LOOP____mul1 <- [];
    trace_h__MUL__LOOP____mul1 <-
    (trace_h__MUL__LOOP____mul1 ++ [(Assert, (BArray256.is_init b_b 0 256))]);
    lo <- (BArray256.get64 b 0);
    (hi, lo) <- (mulu_64 lo a);
    b_r <- (BArray512.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 0 lo);
    c <- hi;
    i <- 1;
    while ((i < 32)) {
      trace_h__MUL__LOOP____mul1 <-
      (trace_h__MUL__LOOP____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      lo <- (BArray256.get64 b i);
      (hi, lo) <- (mulu_64 lo a);
      (cf, lo) <- (adc_64 lo c false);
      ( _0, hi) <- (adc_64 hi (W64.of_int 0) cf);
      trace_h__MUL__LOOP____mul1 <-
      (trace_h__MUL__LOOP____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r i lo);
      c <- hi;
      i <- (i + 1);
    }
    trace_h__MUL__LOOP____mul1 <-
    (trace_h__MUL__LOOP____mul1 ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 8) <= 512)))]);
    b_r <- (BArray512.set64d b_r (32 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 32 c);
    return (r, b_r, trace_h__MUL__LOOP____mul1);
  }
  proc h__MUL__LOOP____mul1acc (k:W64.t, r:BArray512.t, b_r:BArray512.t,
                                a:W64.t, b:BArray256.t, b_b:BArray256.t) : 
  BArray512.t * BArray512.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var lo:W64.t;
    var hi:W64.t;
    var cf:bool;
    var c:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__LOOP____mul1acc:trace;
    trace_h__MUL__LOOP____mul1acc <- [];
    trace_h__MUL__LOOP____mul1acc <-
    (trace_h__MUL__LOOP____mul1acc ++
    [(Assert,
     ((((1 <= (W64.to_uint k)) /\ ((W64.to_uint k) < 32)) /\
      (BArray512.is_init b_r 0 (8 * ((W64.to_uint k) + 32)))) /\
     (BArray256.is_init b_b 0 256)))]);
    lo <- (BArray256.get64 b 0);
    (hi, lo) <- (mulu_64 lo a);
    trace_h__MUL__LOOP____mul1acc <-
    (trace_h__MUL__LOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 512)))]);
    trace_h__MUL__LOOP____mul1acc <-
    (trace_h__MUL__LOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 512)))]);
    trace_h__MUL__LOOP____mul1acc <-
    (trace_h__MUL__LOOP____mul1acc ++
    [(Assert, (BArray512.is_init b_r ((W64.to_uint k) * 8) 8))]);
    b_r <-
    (BArray512.set64d b_r ((W64.to_uint k) * 8)
    (W64.of_int 18446744073709551615));
    (aux, aux_0) <- (adc_64 (BArray512.get64 r (W64.to_uint k)) lo false);
    cf <- aux;
    r <- (BArray512.set64 r (W64.to_uint k) aux_0);
    ( _0, hi) <- (adc_64 hi (W64.of_int 0) cf);
    c <- hi;
    i <- 1;
    while ((i < 32)) {
      trace_h__MUL__LOOP____mul1acc <-
      (trace_h__MUL__LOOP____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      lo <- (BArray256.get64 b i);
      (hi, lo) <- (mulu_64 lo a);
      trace_h__MUL__LOOP____mul1acc <-
      (trace_h__MUL__LOOP____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 512)))]);
      trace_h__MUL__LOOP____mul1acc <-
      (trace_h__MUL__LOOP____mul1acc ++
      [(Assert,
       (BArray512.is_init b_r ((W64.to_uint (k + (W64.of_int i))) * 8) 8))]);
      (cf, lo) <-
      (adc_64 lo (BArray512.get64 r (W64.to_uint (k + (W64.of_int i)))) false
      );
      ( _1, hi) <- (adc_64 hi (W64.of_int 0) cf);
      (cf, lo) <- (adc_64 lo c false);
      ( _2, hi) <- (adc_64 hi (W64.of_int 0) cf);
      trace_h__MUL__LOOP____mul1acc <-
      (trace_h__MUL__LOOP____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r ((W64.to_uint (k + (W64.of_int i))) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r (W64.to_uint (k + (W64.of_int i))) lo);
      c <- hi;
      i <- (i + 1);
    }
    trace_h__MUL__LOOP____mul1acc <-
    (trace_h__MUL__LOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint (k + (W64.of_int 32))) * 8)) /\
     ((((W64.to_uint (k + (W64.of_int 32))) * 8) + 8) <= 512)))]);
    b_r <-
    (BArray512.set64d b_r ((W64.to_uint (k + (W64.of_int 32))) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r (W64.to_uint (k + (W64.of_int 32))) c);
    return (r, b_r, trace_h__MUL__LOOP____mul1acc);
  }
  proc h__MUL__LOOP___os_muln (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                               b_a:BArray256.t, b:BArray256.t,
                               b_b:BArray256.t) : BArray512.t * BArray512.t *
                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var aux_1:BArray512.t;
    var aux_2:BArray512.t;
    var ai:W64.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:W64.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray512.t;
    var param_3:BArray512.t;
    var param_4:W64.t;
    var param_5:BArray256.t;
    var result_0:BArray512.t;
    var b_result_0:BArray512.t;
    var trace_h__MUL__LOOP___os_muln:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__MUL__LOOP___os_muln <- [];
    trace_h__MUL__LOOP___os_muln <-
    (trace_h__MUL__LOOP___os_muln ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    ai <- (BArray256.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__LOOP____mul1 (param, b_param,
    param_0, param_1, (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__LOOP___os_muln <-
    (trace_h__MUL__LOOP___os_muln ++ tmp__trace);
    trace_h__MUL__LOOP___os_muln <-
    (trace_h__MUL__LOOP___os_muln ++
    [(Assert, (BArray512.is_init b_result 0 264))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 32))) {
      trace_h__MUL__LOOP___os_muln <-
      (trace_h__MUL__LOOP___os_muln ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 256)))]);
      ai <- (BArray256.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__LOOP____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray256.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__LOOP___os_muln <-
      (trace_h__MUL__LOOP___os_muln ++ tmp__trace);
      trace_h__MUL__LOOP___os_muln <-
      (trace_h__MUL__LOOP___os_muln ++
      [(Assert,
       (BArray512.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 32) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__MUL__LOOP___os_muln);
  }
  proc h__MUL__LOOP___os_muln_ (r:BArray512.t, b_r:BArray512.t,
                                a:BArray256.t, b_a:BArray256.t,
                                b:BArray256.t, b_b:BArray256.t) : BArray512.t *
                                                                  BArray512.t *
                                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__MUL__LOOP___os_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MUL__LOOP___os_muln_ <- [];
    trace_h__MUL__LOOP___os_muln_ <-
    (trace_h__MUL__LOOP___os_muln_ ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__LOOP___os_muln (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__LOOP___os_muln_ <-
    (trace_h__MUL__LOOP___os_muln_ ++ tmp__trace);
    trace_h__MUL__LOOP___os_muln_ <-
    (trace_h__MUL__LOOP___os_muln_ ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    r <- r;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__LOOP___os_muln_);
  }
  proc h__MUL__LOOP___os_sqrn (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                               b_a:BArray256.t) : BArray512.t * BArray512.t *
                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var aux_1:BArray512.t;
    var aux_2:BArray512.t;
    var ai:W64.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:W64.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray512.t;
    var param_3:BArray512.t;
    var param_4:W64.t;
    var param_5:BArray256.t;
    var result_0:BArray512.t;
    var b_result_0:BArray512.t;
    var trace_h__MUL__LOOP___os_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__MUL__LOOP___os_sqrn <- [];
    trace_h__MUL__LOOP___os_sqrn <-
    (trace_h__MUL__LOOP___os_sqrn ++
    [(Assert, (BArray256.is_init b_a 0 256))]);
    ai <- (BArray256.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__LOOP____mul1 (param, b_param,
    param_0, param_1, (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__LOOP___os_sqrn <-
    (trace_h__MUL__LOOP___os_sqrn ++ tmp__trace);
    trace_h__MUL__LOOP___os_sqrn <-
    (trace_h__MUL__LOOP___os_sqrn ++
    [(Assert, (BArray512.is_init b_result 0 264))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 32))) {
      trace_h__MUL__LOOP___os_sqrn <-
      (trace_h__MUL__LOOP___os_sqrn ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 256)))]);
      ai <- (BArray256.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- a;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__LOOP____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray256.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__LOOP___os_sqrn <-
      (trace_h__MUL__LOOP___os_sqrn ++ tmp__trace);
      trace_h__MUL__LOOP___os_sqrn <-
      (trace_h__MUL__LOOP___os_sqrn ++
      [(Assert,
       (BArray512.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 32) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__MUL__LOOP___os_sqrn);
  }
  proc h__MUL__LOOP___os_sqrn_ (r:BArray512.t, b_r:BArray512.t,
                                a:BArray256.t, b_a:BArray256.t) : BArray512.t *
                                                                  BArray512.t *
                                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__MUL__LOOP___os_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__LOOP___os_sqrn_ <- [];
    trace_h__MUL__LOOP___os_sqrn_ <-
    (trace_h__MUL__LOOP___os_sqrn_ ++
    [(Assert, (BArray256.is_init b_a 0 256))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__LOOP___os_sqrn (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__LOOP___os_sqrn_ <-
    (trace_h__MUL__LOOP___os_sqrn_ ++ tmp__trace);
    trace_h__MUL__LOOP___os_sqrn_ <-
    (trace_h__MUL__LOOP___os_sqrn_ ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    r <- r;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__LOOP___os_sqrn_);
  }
  proc h__MUL__LOOP____mont_redM (r:BArray256.t, b_r:BArray256.t,
                                  a:BArray512.t, b_a:BArray512.t,
                                  _P_mP:BArray512.t, b__P_mP:BArray512.t,
                                  _U0:W64.t) : BArray256.t * BArray256.t *
                                               trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var i:int;
    var lo:W64.t;
    var c:W64.t;
    var k:W64.t;
    var m:W64.t;
    var hi:W64.t;
    var cf:bool;
    var w:W64.t;
    var b_mP:BArray256.t;
    var mP:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var b_param_0:BArray256.t;
    var param_0:BArray256.t;
    var param_1:W64.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var trace_h__MUL__LOOP____mont_redM:trace;
    b_mP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    mP <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__LOOP____mont_redM <- [];
    trace_h__MUL__LOOP____mont_redM <-
    (trace_h__MUL__LOOP____mont_redM ++
    [(Assert,
     ((BArray512.is_init b_a 0 512) /\ (BArray512.is_init b__P_mP 0 512)))]);
    i <- 0;
    while ((i < 32)) {
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
      lo <- (BArray512.get64 a i);
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r i lo);
      i <- (i + 1);
    }
    c <- (W64.of_int 0);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 32))) {
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, (BArray256.is_init b_r 0 8))]);
      m <- (BArray256.get64 r 0);
      m <- (m * _U0);
      lo <- (BArray512.get64 _P_mP 0);
      (hi, lo) <- (mulu_64 lo m);
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, (BArray256.is_init b_r 0 8))]);
      (cf, lo) <- (adc_64 lo (BArray256.get64 r 0) false);
      ( _0, hi) <- (adc_64 hi (W64.of_int 0) cf);
      w <- hi;
      i <- 1;
      while ((i < 32)) {
        trace_h__MUL__LOOP____mont_redM <-
        (trace_h__MUL__LOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
        lo <- (BArray512.get64 _P_mP i);
        (hi, lo) <- (mulu_64 lo m);
        trace_h__MUL__LOOP____mont_redM <-
        (trace_h__MUL__LOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
        trace_h__MUL__LOOP____mont_redM <-
        (trace_h__MUL__LOOP____mont_redM ++
        [(Assert, (BArray256.is_init b_r (i * 8) 8))]);
        (cf, lo) <- (adc_64 lo (BArray256.get64 r i) false);
        ( _1, hi) <- (adc_64 hi (W64.of_int 0) cf);
        (cf, lo) <- (adc_64 lo w false);
        ( _2, hi) <- (adc_64 hi (W64.of_int 0) cf);
        trace_h__MUL__LOOP____mont_redM <-
        (trace_h__MUL__LOOP____mont_redM ++
        [(Assert, ((0 <= ((i - 1) * 8)) /\ ((((i - 1) * 8) + 8) <= 256)))]);
        b_r <-
        (BArray256.set64d b_r ((i - 1) * 8) (W64.of_int 18446744073709551615)
        );
        r <- (BArray256.set64 r (i - 1) lo);
        w <- hi;
        i <- (i + 1);
      }
      ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int 32))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int 32))) * 8) + 8) <= 512)))]);
      (cf, w) <-
      (adc_64 w (BArray512.get64 a (W64.to_uint (k + (W64.of_int 32)))) cf);
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, ((0 <= ((32 - 1) * 8)) /\ ((((32 - 1) * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r ((32 - 1) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r (32 - 1) w);
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + (W64.of_int 1));
    }
    trace_h__MUL__LOOP____mont_redM <-
    (trace_h__MUL__LOOP____mont_redM ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 256) <= 512)))]);
    b_mP <- (SBArray512_256.get_sub64 b__P_mP 32);
    mP <- (SBArray512_256.get_sub64 _P_mP 32);
    b_param <- b_r;
    param <- r;
    b_param_0 <- b_mP;
    param_0 <- mP;
    param_1 <- c;
    (aux, aux_0, tmp__trace) <@ h__BN___cminusP_ (param, b_param, param_0,
    b_param_0, param_1);
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__LOOP____mont_redM <-
    (trace_h__MUL__LOOP____mont_redM ++ tmp__trace);
    trace_h__MUL__LOOP____mont_redM <-
    (trace_h__MUL__LOOP____mont_redM ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__LOOP____mont_redM);
  }
  proc h__MUL__XUNR____mul1 (r:BArray512.t, b_r:BArray512.t, a:W64.t,
                             b:BArray256.t, b_b:BArray256.t) : BArray512.t *
                                                               BArray512.t *
                                                               trace = {
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var i:int;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__MUL__XUNR____mul1:trace;
    trace_h__MUL__XUNR____mul1 <- [];
    trace_h__MUL__XUNR____mul1 <-
    (trace_h__MUL__XUNR____mul1 ++ [(Assert, (BArray256.is_init b_b 0 256))]);
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray256.get64 b 0));
    b_r <- (BArray512.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 0 lo);
    i <- 1;
    while ((i < 32)) {
      t <- hi;
      trace_h__MUL__XUNR____mul1 <-
      (trace_h__MUL__XUNR____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      (hi, lo) <- (MULX_64 a (BArray256.get64 b i));
      (cf, t) <- (ADCX_64 t lo cf);
      trace_h__MUL__XUNR____mul1 <-
      (trace_h__MUL__XUNR____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r i t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    trace_h__MUL__XUNR____mul1 <-
    (trace_h__MUL__XUNR____mul1 ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 8) <= 512)))]);
    b_r <- (BArray512.set64d b_r (32 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 32 hi);
    return (r, b_r, trace_h__MUL__XUNR____mul1);
  }
  proc h__MUL__XUNR____mul1acc (k:int, r:BArray512.t, b_r:BArray512.t,
                                a:W64.t, b:BArray256.t, b_b:BArray256.t) : 
  BArray512.t * BArray512.t * trace = {
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var t:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XUNR____mul1acc:trace;
    trace_h__MUL__XUNR____mul1acc <- [];
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert,
     ((((1 <= k) /\ (k < 32)) /\ (BArray512.is_init b_r 0 (8 * (k + 32)))) /\
     (BArray256.is_init b_b 0 256)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray256.get64 b 0));
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert, (BArray512.is_init b_r (k * 8) 8))]);
    t <- (BArray512.get64 r k);
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
    b_r <- (BArray512.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r k t);
    i <- 1;
    while ((i < 32)) {
      trace_h__MUL__XUNR____mul1acc <-
      (trace_h__MUL__XUNR____mul1acc ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 512)))]);
      trace_h__MUL__XUNR____mul1acc <-
      (trace_h__MUL__XUNR____mul1acc ++
      [(Assert, (BArray512.is_init b_r ((k + i) * 8) 8))]);
      t <- (BArray512.get64 r (k + i));
      (cf, t) <- (ADCX_64 t hi cf);
      trace_h__MUL__XUNR____mul1acc <-
      (trace_h__MUL__XUNR____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      (hi, lo) <- (MULX_64 a (BArray256.get64 b i));
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__MUL__XUNR____mul1acc <-
      (trace_h__MUL__XUNR____mul1acc ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r ((k + i) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r (k + i) t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert, ((0 <= ((k + 32) * 8)) /\ ((((k + 32) * 8) + 8) <= 512)))]);
    b_r <-
    (BArray512.set64d b_r ((k + 32) * 8) (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r (k + 32) hi);
    return (r, b_r, trace_h__MUL__XUNR____mul1acc);
  }
  proc h__MUL__XUNR___os_muln (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                               b_a:BArray256.t, b:BArray256.t,
                               b_b:BArray256.t) : BArray512.t * BArray512.t *
                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var aux_1:BArray512.t;
    var aux_2:BArray512.t;
    var ai:W64.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:W64.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var k:int;
    var param_2:int;
    var b_param_0:BArray512.t;
    var param_3:BArray512.t;
    var param_4:W64.t;
    var param_5:BArray256.t;
    var result_0:BArray512.t;
    var b_result_0:BArray512.t;
    var trace_h__MUL__XUNR___os_muln:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__MUL__XUNR___os_muln <- [];
    trace_h__MUL__XUNR___os_muln <-
    (trace_h__MUL__XUNR___os_muln ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    ai <- (BArray256.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XUNR____mul1 (param, b_param,
    param_0, param_1, (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XUNR___os_muln <-
    (trace_h__MUL__XUNR___os_muln ++ tmp__trace);
    trace_h__MUL__XUNR___os_muln <-
    (trace_h__MUL__XUNR___os_muln ++
    [(Assert, (BArray512.is_init b_result 0 264))]);
    b_r <- b_result;
    r <- result;
    k <- 1;
    while ((k < 32)) {
      trace_h__MUL__XUNR___os_muln <-
      (trace_h__MUL__XUNR___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      ai <- (BArray256.get64 a k);
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__XUNR____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray256.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__XUNR___os_muln <-
      (trace_h__MUL__XUNR___os_muln ++ tmp__trace);
      trace_h__MUL__XUNR___os_muln <-
      (trace_h__MUL__XUNR___os_muln ++
      [(Assert, (BArray512.is_init b_result_0 0 (8 * ((param_2 + 32) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + 1);
    }
    return (r, b_r, trace_h__MUL__XUNR___os_muln);
  }
  proc h__MUL__XUNR___os_muln_ (r:BArray512.t, b_r:BArray512.t,
                                a:BArray256.t, b_a:BArray256.t,
                                b:BArray256.t, b_b:BArray256.t) : BArray512.t *
                                                                  BArray512.t *
                                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__MUL__XUNR___os_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MUL__XUNR___os_muln_ <- [];
    trace_h__MUL__XUNR___os_muln_ <-
    (trace_h__MUL__XUNR___os_muln_ ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XUNR___os_muln (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XUNR___os_muln_ <-
    (trace_h__MUL__XUNR___os_muln_ ++ tmp__trace);
    trace_h__MUL__XUNR___os_muln_ <-
    (trace_h__MUL__XUNR___os_muln_ ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    r <- r;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XUNR___os_muln_);
  }
  proc h__MUL__XUNR____sqr_row0 (r:BArray512.t, b_r:BArray512.t,
                                 a:BArray256.t, b_a:BArray256.t) : BArray512.t *
                                                                   BArray512.t *
                                                                   trace = {
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var j:int;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__MUL__XUNR____sqr_row0:trace;
    trace_h__MUL__XUNR____sqr_row0 <- [];
    trace_h__MUL__XUNR____sqr_row0 <-
    (trace_h__MUL__XUNR____sqr_row0 ++
    [(Assert, ((2 <= 32) /\ (BArray256.is_init b_a 0 256)))]);
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    ai <- (BArray256.get64 a 0);
    (hi, lo) <- (MULX_64 ai (BArray256.get64 a 1));
    b_r <- (BArray512.set64d b_r 8 (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 1 lo);
    j <- 2;
    while ((j < 32)) {
      t <- hi;
      trace_h__MUL__XUNR____sqr_row0 <-
      (trace_h__MUL__XUNR____sqr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 256)))]);
      (hi, lo) <- (MULX_64 ai (BArray256.get64 a j));
      (cf, t) <- (ADCX_64 t lo cf);
      trace_h__MUL__XUNR____sqr_row0 <-
      (trace_h__MUL__XUNR____sqr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (j * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r j t);
      j <- (j + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    trace_h__MUL__XUNR____sqr_row0 <-
    (trace_h__MUL__XUNR____sqr_row0 ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 8) <= 512)))]);
    b_r <- (BArray512.set64d b_r (32 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 32 hi);
    return (r, b_r, trace_h__MUL__XUNR____sqr_row0);
  }
  proc h__MUL__XUNR____sqr_rowacc (i:int, r:BArray512.t, b_r:BArray512.t,
                                   a:BArray256.t, b_a:BArray256.t) : 
  BArray512.t * BArray512.t * trace = {
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var t:W64.t;
    var j:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XUNR____sqr_rowacc:trace;
    trace_h__MUL__XUNR____sqr_rowacc <- [];
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert,
     ((((1 <= i) /\ (i < (32 - 1))) /\
      (BArray512.is_init b_r 8 (8 * ((i + 32) - 1)))) /\
     (BArray256.is_init b_a 0 256)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
    ai <- (BArray256.get64 a i);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert, ((0 <= ((i + 1) * 8)) /\ ((((i + 1) * 8) + 8) <= 256)))]);
    (hi, lo) <- (MULX_64 ai (BArray256.get64 a (i + 1)));
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert,
     ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 512)))]);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert, (BArray512.is_init b_r (((2 * i) + 1) * 8) 8))]);
    t <- (BArray512.get64 r ((2 * i) + 1));
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert,
     ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 512)))]);
    b_r <-
    (BArray512.set64d b_r (((2 * i) + 1) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r ((2 * i) + 1) t);
    j <- (i + 2);
    while ((j < 32)) {
      trace_h__MUL__XUNR____sqr_rowacc <-
      (trace_h__MUL__XUNR____sqr_rowacc ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 512)))]);
      trace_h__MUL__XUNR____sqr_rowacc <-
      (trace_h__MUL__XUNR____sqr_rowacc ++
      [(Assert, (BArray512.is_init b_r ((i + j) * 8) 8))]);
      t <- (BArray512.get64 r (i + j));
      (cf, t) <- (ADCX_64 t hi cf);
      trace_h__MUL__XUNR____sqr_rowacc <-
      (trace_h__MUL__XUNR____sqr_rowacc ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 256)))]);
      (hi, lo) <- (MULX_64 ai (BArray256.get64 a j));
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__MUL__XUNR____sqr_rowacc <-
      (trace_h__MUL__XUNR____sqr_rowacc ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r ((i + j) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r (i + j) t);
      j <- (j + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert, ((0 <= ((i + 32) * 8)) /\ ((((i + 32) * 8) + 8) <= 512)))]);
    b_r <-
    (BArray512.set64d b_r ((i + 32) * 8) (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r (i + 32) hi);
    return (r, b_r, trace_h__MUL__XUNR____sqr_rowacc);
  }
  proc h__MUL__XUNR____sqr_diag (r:BArray512.t, b_r:BArray512.t,
                                 a:BArray256.t, b_a:BArray256.t) : BArray512.t *
                                                                   BArray512.t *
                                                                   trace = {
    var inc:int;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var t:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XUNR____sqr_diag:trace;
    trace_h__MUL__XUNR____sqr_diag <- [];
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert,
     (((2 <= 32) /\ (BArray512.is_init b_r 8 496)) /\
     (BArray256.is_init b_a 0 256)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    ai <- (BArray256.get64 a 0);
    (hi, lo) <- (MULX_64 ai (BArray256.get64 a 0));
    b_r <- (BArray512.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 0 lo);
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert, (BArray512.is_init b_r 8 8))]);
    t <- (BArray512.get64 r 1);
    (cf, t) <- (ADCX_64 t t cf);
    (of_0, t) <- (ADOX_64 t hi of_0);
    b_r <- (BArray512.set64d b_r 8 (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 1 t);
    inc <- (32 - 1);
    i <- 1;
    while ((i < inc)) {
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      ai <- (BArray256.get64 a i);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      (hi, lo) <- (MULX_64 ai (BArray256.get64 a i));
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= ((2 * i) * 8)) /\ ((((2 * i) * 8) + 8) <= 512)))]);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, (BArray512.is_init b_r ((2 * i) * 8) 8))]);
      t <- (BArray512.get64 r (2 * i));
      (cf, t) <- (ADCX_64 t t cf);
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= ((2 * i) * 8)) /\ ((((2 * i) * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r ((2 * i) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r (2 * i) t);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert,
       ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 512)))]);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, (BArray512.is_init b_r (((2 * i) + 1) * 8) 8))]);
      t <- (BArray512.get64 r ((2 * i) + 1));
      (cf, t) <- (ADCX_64 t t cf);
      (of_0, t) <- (ADOX_64 t hi of_0);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert,
       ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (((2 * i) + 1) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r ((2 * i) + 1) t);
      i <- (i + 1);
    }
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert, ((0 <= ((32 - 1) * 8)) /\ ((((32 - 1) * 8) + 8) <= 256)))]);
    ai <- (BArray256.get64 a (32 - 1));
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert, ((0 <= ((32 - 1) * 8)) /\ ((((32 - 1) * 8) + 8) <= 256)))]);
    (hi, lo) <- (MULX_64 ai (BArray256.get64 a (32 - 1)));
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert,
     ((0 <= (((2 * 32) - 2) * 8)) /\ (((((2 * 32) - 2) * 8) + 8) <= 512)))]);
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert, (BArray512.is_init b_r (((2 * 32) - 2) * 8) 8))]);
    t <- (BArray512.get64 r ((2 * 32) - 2));
    (cf, t) <- (ADCX_64 t t cf);
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert,
     ((0 <= (((2 * 32) - 2) * 8)) /\ (((((2 * 32) - 2) * 8) + 8) <= 512)))]);
    b_r <-
    (BArray512.set64d b_r (((2 * 32) - 2) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r ((2 * 32) - 2) t);
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert,
     ((0 <= (((2 * 32) - 1) * 8)) /\ (((((2 * 32) - 1) * 8) + 8) <= 512)))]);
    b_r <-
    (BArray512.set64d b_r (((2 * 32) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r ((2 * 32) - 1) hi);
    return (r, b_r, trace_h__MUL__XUNR____sqr_diag);
  }
  proc h__MUL__XUNR___os_sqrn (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                               b_a:BArray256.t) : BArray512.t * BArray512.t *
                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var aux_1:BArray512.t;
    var aux_2:BArray512.t;
    var aux_3:BArray512.t;
    var aux_4:BArray512.t;
    var inc:int;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var i:int;
    var param_1:int;
    var b_param_0:BArray512.t;
    var param_2:BArray512.t;
    var param_3:BArray256.t;
    var result_0:BArray512.t;
    var b_result_0:BArray512.t;
    var b_param_1:BArray512.t;
    var param_4:BArray512.t;
    var param_5:BArray256.t;
    var result_1:BArray512.t;
    var b_result_1:BArray512.t;
    var trace_h__MUL__XUNR___os_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    param <- witness;
    param_0 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_h__MUL__XUNR___os_sqrn <- [];
    trace_h__MUL__XUNR___os_sqrn <-
    (trace_h__MUL__XUNR___os_sqrn ++
    [(Assert, (BArray256.is_init b_a 0 256))]);
    if ((32 = 1)) {
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 256)))]);
      ai <- (BArray256.get64 a 0);
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 256)))]);
      (hi, lo) <- (MULX_64 ai (BArray256.get64 a 0));
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (0 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r 0 lo);
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (1 * 8)) /\ (((1 * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (1 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r 1 hi);
    } else {
      b_param <- b_r;
      param <- r;
      param_0 <- a;
      (aux, aux_0, tmp__trace) <@ h__MUL__XUNR____sqr_row0 (param, b_param,
      param_0, (BArray256.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++ tmp__trace);
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, (BArray512.is_init b_result 8 256))]);
      b_r <- b_result;
      r <- result;
      inc <- (32 - 1);
      i <- 1;
      while ((i < inc)) {
        param_1 <- i;
        b_param_0 <- b_r;
        param_2 <- r;
        param_3 <- a;
        (aux_1, aux_2, tmp__trace) <@ h__MUL__XUNR____sqr_rowacc (param_1,
        param_2, b_param_0, param_3, (BArray256.init_arr (W8.of_int 255)));
        result_0 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__MUL__XUNR___os_sqrn <-
        (trace_h__MUL__XUNR___os_sqrn ++ tmp__trace);
        trace_h__MUL__XUNR___os_sqrn <-
        (trace_h__MUL__XUNR___os_sqrn ++
        [(Assert, (BArray512.is_init b_result_0 8 (8 * (param_1 + 32))))]);
        b_r <- b_result_0;
        r <- result_0;
        i <- (i + 1);
      }
      b_param_1 <- b_r;
      param_4 <- r;
      param_5 <- a;
      (aux_3, aux_4, tmp__trace) <@ h__MUL__XUNR____sqr_diag (param_4,
      b_param_1, param_5, (BArray256.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++ tmp__trace);
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, (BArray512.is_init b_result_1 0 512))]);
      b_r <- (BArray512.init_arr (W8.of_int 255));
      r <- result_1;
    }
    return (r, b_r, trace_h__MUL__XUNR___os_sqrn);
  }
  proc h__MUL__XUNR___os_sqrn_ (r:BArray512.t, b_r:BArray512.t,
                                a:BArray256.t, b_a:BArray256.t) : BArray512.t *
                                                                  BArray512.t *
                                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__MUL__XUNR___os_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__XUNR___os_sqrn_ <- [];
    trace_h__MUL__XUNR___os_sqrn_ <-
    (trace_h__MUL__XUNR___os_sqrn_ ++
    [(Assert, (BArray256.is_init b_a 0 256))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__XUNR___os_sqrn (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XUNR___os_sqrn_ <-
    (trace_h__MUL__XUNR___os_sqrn_ ++ tmp__trace);
    trace_h__MUL__XUNR___os_sqrn_ <-
    (trace_h__MUL__XUNR___os_sqrn_ ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    r <- r;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XUNR___os_sqrn_);
  }
  proc h__MUL__XUNR____mont_redM (r:BArray256.t, b_r:BArray256.t,
                                  a:BArray512.t, b_a:BArray512.t,
                                  _P_mP:BArray512.t, b__P_mP:BArray512.t,
                                  _U0:W64.t) : BArray256.t * BArray256.t *
                                               trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var c:W64.t;
    var w0:W64.t;
    var k:int;
    var m:W64.t;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var i:int;
    var t:W64.t;
    var b_mP:BArray256.t;
    var mP:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var b_param_0:BArray256.t;
    var param_0:BArray256.t;
    var param_1:W64.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var trace_h__MUL__XUNR____mont_redM:trace;
    b_mP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    mP <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__XUNR____mont_redM <- [];
    trace_h__MUL__XUNR____mont_redM <-
    (trace_h__MUL__XUNR____mont_redM ++
    [(Assert,
     ((BArray512.is_init b_a 0 512) /\ (BArray512.is_init b__P_mP 0 512)))]);
    c <- (W64.of_int 0);
    w0 <- (BArray512.get64 a 0);
    k <- 0;
    while ((k < 32)) {
      m <- w0;
      m <- (m * _U0);
      (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
      (hi, lo) <- (MULX_64 m (BArray512.get64 _P_mP 0));
      (of_0, w0) <- (ADOX_64 w0 lo of_0);
      i <- 1;
      while ((i < 32)) {
        if ((k = 0)) {
          trace_h__MUL__XUNR____mont_redM <-
          (trace_h__MUL__XUNR____mont_redM ++
          [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
          t <- (BArray512.get64 a i);
        } else {
          trace_h__MUL__XUNR____mont_redM <-
          (trace_h__MUL__XUNR____mont_redM ++
          [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
          trace_h__MUL__XUNR____mont_redM <-
          (trace_h__MUL__XUNR____mont_redM ++
          [(Assert, (BArray256.is_init b_r (i * 8) 8))]);
          t <- (BArray256.get64 r i);
        }
        (cf, t) <- (ADCX_64 t hi cf);
        trace_h__MUL__XUNR____mont_redM <-
        (trace_h__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
        (hi, lo) <- (MULX_64 m (BArray512.get64 _P_mP i));
        (of_0, t) <- (ADOX_64 t lo of_0);
        trace_h__MUL__XUNR____mont_redM <-
        (trace_h__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= ((i - 1) * 8)) /\ ((((i - 1) * 8) + 8) <= 256)))]);
        b_r <-
        (BArray256.set64d b_r ((i - 1) * 8) (W64.of_int 18446744073709551615)
        );
        r <- (BArray256.set64 r (i - 1) t);
        if ((i = 1)) {
          w0 <- t;
        } else {
          
        }
        i <- (i + 1);
      }
      (cf, hi) <- (ADCX_64 hi _zero cf);
      (of_0, hi) <- (ADOX_64 hi _zero of_0);
      if ((k = 0)) {
        trace_h__MUL__XUNR____mont_redM <-
        (trace_h__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 8) <= 512)))]);
        (cf, hi) <- (adc_64 hi (BArray512.get64 a 32) false);
      } else {
        ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
        trace_h__MUL__XUNR____mont_redM <-
        (trace_h__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= ((k + 32) * 8)) /\ ((((k + 32) * 8) + 8) <= 512)))]);
        (cf, hi) <- (adc_64 hi (BArray512.get64 a (k + 32)) cf);
      }
      trace_h__MUL__XUNR____mont_redM <-
      (trace_h__MUL__XUNR____mont_redM ++
      [(Assert, ((0 <= ((32 - 1) * 8)) /\ ((((32 - 1) * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r ((32 - 1) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r (32 - 1) hi);
      if ((32 = 1)) {
        w0 <- hi;
      } else {
        
      }
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + 1);
    }
    trace_h__MUL__XUNR____mont_redM <-
    (trace_h__MUL__XUNR____mont_redM ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 256) <= 512)))]);
    b_mP <- (SBArray512_256.get_sub64 b__P_mP 32);
    mP <- (SBArray512_256.get_sub64 _P_mP 32);
    b_param <- b_r;
    param <- r;
    b_param_0 <- b_mP;
    param_0 <- mP;
    param_1 <- c;
    (aux, aux_0, tmp__trace) <@ h__BN___cminusP_ (param, b_param, param_0,
    b_param_0, param_1);
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XUNR____mont_redM <-
    (trace_h__MUL__XUNR____mont_redM ++ tmp__trace);
    trace_h__MUL__XUNR____mont_redM <-
    (trace_h__MUL__XUNR____mont_redM ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XUNR____mont_redM);
  }
  proc h__MUL__XLOOP____mul1 (r:BArray512.t, b_r:BArray512.t, a:W64.t,
                              b:BArray256.t, b_b:BArray256.t) : BArray512.t *
                                                                BArray512.t *
                                                                trace = {
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var i:int;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__MUL__XLOOP____mul1:trace;
    trace_h__MUL__XLOOP____mul1 <- [];
    trace_h__MUL__XLOOP____mul1 <-
    (trace_h__MUL__XLOOP____mul1 ++
    [(Assert, (BArray256.is_init b_b 0 256))]);
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray256.get64 b 0));
    b_r <- (BArray512.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 0 lo);
    i <- 1;
    while ((i < 32)) {
      t <- hi;
      trace_h__MUL__XLOOP____mul1 <-
      (trace_h__MUL__XLOOP____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      (hi, lo) <- (MULX_64 a (BArray256.get64 b i));
      (cf, t) <- (ADCX_64 t lo cf);
      trace_h__MUL__XLOOP____mul1 <-
      (trace_h__MUL__XLOOP____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r i t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    trace_h__MUL__XLOOP____mul1 <-
    (trace_h__MUL__XLOOP____mul1 ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 8) <= 512)))]);
    b_r <- (BArray512.set64d b_r (32 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 32 hi);
    return (r, b_r, trace_h__MUL__XLOOP____mul1);
  }
  proc h__MUL__XLOOP____mul1acc (k:W64.t, r:BArray512.t, b_r:BArray512.t,
                                 a:W64.t, b:BArray256.t, b_b:BArray256.t) : 
  BArray512.t * BArray512.t * trace = {
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var t:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XLOOP____mul1acc:trace;
    trace_h__MUL__XLOOP____mul1acc <- [];
    trace_h__MUL__XLOOP____mul1acc <-
    (trace_h__MUL__XLOOP____mul1acc ++
    [(Assert,
     ((((1 <= (W64.to_uint k)) /\ ((W64.to_uint k) < 32)) /\
      (BArray512.is_init b_r 0 (8 * ((W64.to_uint k) + 32)))) /\
     (BArray256.is_init b_b 0 256)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray256.get64 b 0));
    trace_h__MUL__XLOOP____mul1acc <-
    (trace_h__MUL__XLOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 512)))]);
    trace_h__MUL__XLOOP____mul1acc <-
    (trace_h__MUL__XLOOP____mul1acc ++
    [(Assert, (BArray512.is_init b_r ((W64.to_uint k) * 8) 8))]);
    t <- (BArray512.get64 r (W64.to_uint k));
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__MUL__XLOOP____mul1acc <-
    (trace_h__MUL__XLOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 512)))]);
    b_r <-
    (BArray512.set64d b_r ((W64.to_uint k) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r (W64.to_uint k) t);
    i <- 1;
    while ((i < 32)) {
      trace_h__MUL__XLOOP____mul1acc <-
      (trace_h__MUL__XLOOP____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 512)))]);
      trace_h__MUL__XLOOP____mul1acc <-
      (trace_h__MUL__XLOOP____mul1acc ++
      [(Assert,
       (BArray512.is_init b_r ((W64.to_uint (k + (W64.of_int i))) * 8) 8))]);
      t <- (BArray512.get64 r (W64.to_uint (k + (W64.of_int i))));
      (cf, t) <- (ADCX_64 t hi cf);
      trace_h__MUL__XLOOP____mul1acc <-
      (trace_h__MUL__XLOOP____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      (hi, lo) <- (MULX_64 a (BArray256.get64 b i));
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__MUL__XLOOP____mul1acc <-
      (trace_h__MUL__XLOOP____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r ((W64.to_uint (k + (W64.of_int i))) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r (W64.to_uint (k + (W64.of_int i))) t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__MUL__XLOOP____mul1acc <-
    (trace_h__MUL__XLOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint (k + (W64.of_int 32))) * 8)) /\
     ((((W64.to_uint (k + (W64.of_int 32))) * 8) + 8) <= 512)))]);
    b_r <-
    (BArray512.set64d b_r ((W64.to_uint (k + (W64.of_int 32))) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r (W64.to_uint (k + (W64.of_int 32))) hi);
    return (r, b_r, trace_h__MUL__XLOOP____mul1acc);
  }
  proc h__MUL__XLOOP___os_muln (r:BArray512.t, b_r:BArray512.t,
                                a:BArray256.t, b_a:BArray256.t,
                                b:BArray256.t, b_b:BArray256.t) : BArray512.t *
                                                                  BArray512.t *
                                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var aux_1:BArray512.t;
    var aux_2:BArray512.t;
    var ai:W64.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:W64.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray512.t;
    var param_3:BArray512.t;
    var param_4:W64.t;
    var param_5:BArray256.t;
    var result_0:BArray512.t;
    var b_result_0:BArray512.t;
    var trace_h__MUL__XLOOP___os_muln:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__MUL__XLOOP___os_muln <- [];
    trace_h__MUL__XLOOP___os_muln <-
    (trace_h__MUL__XLOOP___os_muln ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    ai <- (BArray256.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XLOOP____mul1 (param, b_param,
    param_0, param_1, (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XLOOP___os_muln <-
    (trace_h__MUL__XLOOP___os_muln ++ tmp__trace);
    trace_h__MUL__XLOOP___os_muln <-
    (trace_h__MUL__XLOOP___os_muln ++
    [(Assert, (BArray512.is_init b_result 0 264))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 32))) {
      trace_h__MUL__XLOOP___os_muln <-
      (trace_h__MUL__XLOOP___os_muln ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 256)))]);
      ai <- (BArray256.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__XLOOP____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray256.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__XLOOP___os_muln <-
      (trace_h__MUL__XLOOP___os_muln ++ tmp__trace);
      trace_h__MUL__XLOOP___os_muln <-
      (trace_h__MUL__XLOOP___os_muln ++
      [(Assert,
       (BArray512.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 32) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__MUL__XLOOP___os_muln);
  }
  proc h__MUL__XLOOP___os_muln_ (r:BArray512.t, b_r:BArray512.t,
                                 a:BArray256.t, b_a:BArray256.t,
                                 b:BArray256.t, b_b:BArray256.t) : BArray512.t *
                                                                   BArray512.t *
                                                                   trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__MUL__XLOOP___os_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MUL__XLOOP___os_muln_ <- [];
    trace_h__MUL__XLOOP___os_muln_ <-
    (trace_h__MUL__XLOOP___os_muln_ ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XLOOP___os_muln (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XLOOP___os_muln_ <-
    (trace_h__MUL__XLOOP___os_muln_ ++ tmp__trace);
    trace_h__MUL__XLOOP___os_muln_ <-
    (trace_h__MUL__XLOOP___os_muln_ ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    r <- r;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XLOOP___os_muln_);
  }
  proc h__MUL__XLOOP___os_sqrn (r:BArray512.t, b_r:BArray512.t,
                                a:BArray256.t, b_a:BArray256.t) : BArray512.t *
                                                                  BArray512.t *
                                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var aux_1:BArray512.t;
    var aux_2:BArray512.t;
    var ai:W64.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:W64.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray512.t;
    var param_3:BArray512.t;
    var param_4:W64.t;
    var param_5:BArray256.t;
    var result_0:BArray512.t;
    var b_result_0:BArray512.t;
    var trace_h__MUL__XLOOP___os_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__MUL__XLOOP___os_sqrn <- [];
    trace_h__MUL__XLOOP___os_sqrn <-
    (trace_h__MUL__XLOOP___os_sqrn ++
    [(Assert, (BArray256.is_init b_a 0 256))]);
    ai <- (BArray256.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__XLOOP____mul1 (param, b_param,
    param_0, param_1, (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XLOOP___os_sqrn <-
    (trace_h__MUL__XLOOP___os_sqrn ++ tmp__trace);
    trace_h__MUL__XLOOP___os_sqrn <-
    (trace_h__MUL__XLOOP___os_sqrn ++
    [(Assert, (BArray512.is_init b_result 0 264))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 32))) {
      trace_h__MUL__XLOOP___os_sqrn <-
      (trace_h__MUL__XLOOP___os_sqrn ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 256)))]);
      ai <- (BArray256.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- a;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__XLOOP____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray256.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__XLOOP___os_sqrn <-
      (trace_h__MUL__XLOOP___os_sqrn ++ tmp__trace);
      trace_h__MUL__XLOOP___os_sqrn <-
      (trace_h__MUL__XLOOP___os_sqrn ++
      [(Assert,
       (BArray512.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 32) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__MUL__XLOOP___os_sqrn);
  }
  proc h__MUL__XLOOP___os_sqrn_ (r:BArray512.t, b_r:BArray512.t,
                                 a:BArray256.t, b_a:BArray256.t) : BArray512.t *
                                                                   BArray512.t *
                                                                   trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__MUL__XLOOP___os_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__XLOOP___os_sqrn_ <- [];
    trace_h__MUL__XLOOP___os_sqrn_ <-
    (trace_h__MUL__XLOOP___os_sqrn_ ++
    [(Assert, (BArray256.is_init b_a 0 256))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__XLOOP___os_sqrn (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XLOOP___os_sqrn_ <-
    (trace_h__MUL__XLOOP___os_sqrn_ ++ tmp__trace);
    trace_h__MUL__XLOOP___os_sqrn_ <-
    (trace_h__MUL__XLOOP___os_sqrn_ ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    r <- r;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XLOOP___os_sqrn_);
  }
  proc h__MUL__XLOOP____mont_redM (r:BArray256.t, b_r:BArray256.t,
                                   a:BArray512.t, b_a:BArray512.t,
                                   _P_mP:BArray512.t, b__P_mP:BArray512.t,
                                   _U0:W64.t) : BArray256.t * BArray256.t *
                                                trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var i:int;
    var t:W64.t;
    var c:W64.t;
    var k:W64.t;
    var m:W64.t;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var b_mP:BArray256.t;
    var mP:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var b_param_0:BArray256.t;
    var param_0:BArray256.t;
    var param_1:W64.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var trace_h__MUL__XLOOP____mont_redM:trace;
    b_mP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    mP <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__XLOOP____mont_redM <- [];
    trace_h__MUL__XLOOP____mont_redM <-
    (trace_h__MUL__XLOOP____mont_redM ++
    [(Assert,
     ((BArray512.is_init b_a 0 512) /\ (BArray512.is_init b__P_mP 0 512)))]);
    i <- 0;
    while ((i < 32)) {
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
      t <- (BArray512.get64 a i);
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r i t);
      i <- (i + 1);
    }
    c <- (W64.of_int 0);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 32))) {
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, (BArray256.is_init b_r 0 8))]);
      m <- (BArray256.get64 r 0);
      m <- (m * _U0);
      (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
      (hi, lo) <- (MULX_64 m (BArray512.get64 _P_mP 0));
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, (BArray256.is_init b_r 0 8))]);
      t <- (BArray256.get64 r 0);
      (of_0, t) <- (ADOX_64 t lo of_0);
      i <- 1;
      while ((i < 32)) {
        trace_h__MUL__XLOOP____mont_redM <-
        (trace_h__MUL__XLOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
        trace_h__MUL__XLOOP____mont_redM <-
        (trace_h__MUL__XLOOP____mont_redM ++
        [(Assert, (BArray256.is_init b_r (i * 8) 8))]);
        t <- (BArray256.get64 r i);
        (cf, t) <- (ADCX_64 t hi cf);
        trace_h__MUL__XLOOP____mont_redM <-
        (trace_h__MUL__XLOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
        (hi, lo) <- (MULX_64 m (BArray512.get64 _P_mP i));
        (of_0, t) <- (ADOX_64 t lo of_0);
        trace_h__MUL__XLOOP____mont_redM <-
        (trace_h__MUL__XLOOP____mont_redM ++
        [(Assert, ((0 <= ((i - 1) * 8)) /\ ((((i - 1) * 8) + 8) <= 256)))]);
        b_r <-
        (BArray256.set64d b_r ((i - 1) * 8) (W64.of_int 18446744073709551615)
        );
        r <- (BArray256.set64 r (i - 1) t);
        i <- (i + 1);
      }
      (cf, hi) <- (ADCX_64 hi _zero cf);
      (of_0, hi) <- (ADOX_64 hi _zero of_0);
      ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int 32))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int 32))) * 8) + 8) <= 512)))]);
      (cf, hi) <-
      (adc_64 hi (BArray512.get64 a (W64.to_uint (k + (W64.of_int 32)))) cf);
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, ((0 <= ((32 - 1) * 8)) /\ ((((32 - 1) * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r ((32 - 1) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r (32 - 1) hi);
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + (W64.of_int 1));
    }
    trace_h__MUL__XLOOP____mont_redM <-
    (trace_h__MUL__XLOOP____mont_redM ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 256) <= 512)))]);
    b_mP <- (SBArray512_256.get_sub64 b__P_mP 32);
    mP <- (SBArray512_256.get_sub64 _P_mP 32);
    b_param <- b_r;
    param <- r;
    b_param_0 <- b_mP;
    param_0 <- mP;
    param_1 <- c;
    (aux, aux_0, tmp__trace) <@ h__BN___cminusP_ (param, b_param, param_0,
    b_param_0, param_1);
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XLOOP____mont_redM <-
    (trace_h__MUL__XLOOP____mont_redM ++ tmp__trace);
    trace_h__MUL__XLOOP____mont_redM <-
    (trace_h__MUL__XLOOP____mont_redM ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XLOOP____mont_redM);
  }
  proc h__MUL__XREG____mulr_row0 (a:W64.t, b:BArray256.t, b_b:BArray256.t) : 
  BArray512.t * BArray512.t * trace = {
    var aux:W64.t;
    var aux_0:W64.t;
    var aux_1:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_3:bool;
    var aux_5:bool;
    var b_t:BArray512.t;
    var cf:bool;
    var _zero:W64.t;
    var t:BArray512.t;
    var i:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__MUL__XREG____mulr_row0:trace;
    b_t <- witness;
    t <- witness;
    trace_h__MUL__XREG____mulr_row0 <- [];
    trace_h__MUL__XREG____mulr_row0 <-
    (trace_h__MUL__XREG____mulr_row0 ++
    [(Assert, (BArray256.is_init b_b 0 256))]);
    b_t <- (BArray512.init_arr (W8.of_int 0));
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    b_t <- (BArray512.set64d b_t 8 (W64.of_int 18446744073709551615));
    b_t <- (BArray512.set64d b_t 0 (W64.of_int 18446744073709551615));
    (aux, aux_0) <- (MULX_64 a (BArray256.get64 b 0));
    t <- (BArray512.set64 t 1 aux);
    t <- (BArray512.set64 t 0 aux_0);
    i <- 1;
    while ((i < 32)) {
      trace_h__MUL__XREG____mulr_row0 <-
      (trace_h__MUL__XREG____mulr_row0 ++
      [(Assert, ((0 <= ((i + 1) * 8)) /\ ((((i + 1) * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____mulr_row0 <-
      (trace_h__MUL__XREG____mulr_row0 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      b_t <-
      (BArray512.set64d b_t ((i + 1) * 8) (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (MULX_64 a (BArray256.get64 b i));
      t <- (BArray512.set64 t (i + 1) aux_1);
      lo <- aux_2;
      trace_h__MUL__XREG____mulr_row0 <-
      (trace_h__MUL__XREG____mulr_row0 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____mulr_row0 <-
      (trace_h__MUL__XREG____mulr_row0 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____mulr_row0 <-
      (trace_h__MUL__XREG____mulr_row0 ++
      [(Assert, (BArray512.is_init b_t (i * 8) 8))]);
      b_t <-
      (BArray512.set64d b_t (i * 8) (W64.of_int 18446744073709551615));
      (aux_3, aux_4) <- (ADCX_64 (BArray512.get64 t i) lo cf);
      cf <- aux_3;
      t <- (BArray512.set64 t i aux_4);
      i <- (i + 1);
    }
    trace_h__MUL__XREG____mulr_row0 <-
    (trace_h__MUL__XREG____mulr_row0 ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____mulr_row0 <-
    (trace_h__MUL__XREG____mulr_row0 ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____mulr_row0 <-
    (trace_h__MUL__XREG____mulr_row0 ++
    [(Assert, (BArray512.is_init b_t (32 * 8) 8))]);
    b_t <- (BArray512.set64d b_t (32 * 8) (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADCX_64 (BArray512.get64 t 32) _zero cf);
    cf <- aux_5;
    t <- (BArray512.set64 t 32 aux_6);
    return (t, b_t, trace_h__MUL__XREG____mulr_row0);
  }
  proc h__MUL__XREG____mulr_rowk (k:int, t:BArray512.t, b_t:BArray512.t,
                                  a:W64.t, b:BArray256.t, b_b:BArray256.t) : 
  BArray512.t * BArray512.t * trace = {
    var aux_0:W64.t;
    var aux_2:W64.t;
    var aux_3:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_8:W64.t;
    var aux_10:W64.t;
    var aux:bool;
    var aux_1:bool;
    var aux_5:bool;
    var aux_7:bool;
    var aux_9:bool;
    var inc:int;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var i:int;
    var hi:W64.t;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XREG____mulr_rowk:trace;
    trace_h__MUL__XREG____mulr_rowk <- [];
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert,
     ((((1 <= k) /\ (k < 32)) /\ (BArray512.is_init b_t 0 (8 * (k + 32)))) /\
     (BArray256.is_init b_b 0 256)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    inc <- (32 - 1);
    i <- 0;
    while ((i < inc)) {
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      (hi, lo) <- (MULX_64 a (BArray256.get64 b i));
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert, (BArray512.is_init b_t ((k + i) * 8) 8))]);
      b_t <-
      (BArray512.set64d b_t ((k + i) * 8) (W64.of_int 18446744073709551615));
      (aux, aux_0) <- (ADOX_64 (BArray512.get64 t (k + i)) lo of_0);
      of_0 <- aux;
      t <- (BArray512.set64 t (k + i) aux_0);
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert,
       ((0 <= (((k + i) + 1) * 8)) /\ (((((k + i) + 1) * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert,
       ((0 <= (((k + i) + 1) * 8)) /\ (((((k + i) + 1) * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert, (BArray512.is_init b_t (((k + i) + 1) * 8) 8))]);
      b_t <-
      (BArray512.set64d b_t (((k + i) + 1) * 8)
      (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (ADCX_64 (BArray512.get64 t ((k + i) + 1)) hi cf);
      cf <- aux_1;
      t <- (BArray512.set64 t ((k + i) + 1) aux_2);
      i <- (i + 1);
    }
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 32) * 8)) /\ ((((k + 32) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((32 - 1) * 8)) /\ ((((32 - 1) * 8) + 8) <= 256)))]);
    b_t <-
    (BArray512.set64d b_t ((k + 32) * 8) (W64.of_int 18446744073709551615));
    (aux_3, aux_4) <- (MULX_64 a (BArray256.get64 b (32 - 1)));
    t <- (BArray512.set64 t (k + 32) aux_3);
    lo <- aux_4;
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert,
     ((0 <= (((k + 32) - 1) * 8)) /\ (((((k + 32) - 1) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert,
     ((0 <= (((k + 32) - 1) * 8)) /\ (((((k + 32) - 1) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, (BArray512.is_init b_t (((k + 32) - 1) * 8) 8))]);
    b_t <-
    (BArray512.set64d b_t (((k + 32) - 1) * 8)
    (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADOX_64 (BArray512.get64 t ((k + 32) - 1)) lo of_0);
    of_0 <- aux_5;
    t <- (BArray512.set64 t ((k + 32) - 1) aux_6);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 32) * 8)) /\ ((((k + 32) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 32) * 8)) /\ ((((k + 32) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, (BArray512.is_init b_t ((k + 32) * 8) 8))]);
    b_t <-
    (BArray512.set64d b_t ((k + 32) * 8) (W64.of_int 18446744073709551615));
    (aux_7, aux_8) <- (ADCX_64 (BArray512.get64 t (k + 32)) _zero cf);
    cf <- aux_7;
    t <- (BArray512.set64 t (k + 32) aux_8);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 32) * 8)) /\ ((((k + 32) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 32) * 8)) /\ ((((k + 32) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, (BArray512.is_init b_t ((k + 32) * 8) 8))]);
    b_t <-
    (BArray512.set64d b_t ((k + 32) * 8) (W64.of_int 18446744073709551615));
    (aux_9, aux_10) <- (ADOX_64 (BArray512.get64 t (k + 32)) _zero of_0);
    of_0 <- aux_9;
    t <- (BArray512.set64 t (k + 32) aux_10);
    return (t, b_t, trace_h__MUL__XREG____mulr_rowk);
  }
  proc h__MUL__XREG___os_muln (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                               b_a:BArray256.t, b:BArray256.t,
                               b_b:BArray256.t) : BArray512.t * BArray512.t *
                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var aux_1:BArray512.t;
    var aux_2:BArray512.t;
    var inc:int;
    var ak:W64.t;
    var param:W64.t;
    var param_0:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var b_t:BArray512.t;
    var t:BArray512.t;
    var k:int;
    var param_1:int;
    var b_param:BArray512.t;
    var param_2:BArray512.t;
    var param_3:W64.t;
    var param_4:BArray256.t;
    var result_0:BArray512.t;
    var b_result_0:BArray512.t;
    var trace_h__MUL__XREG___os_muln:trace;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_t <- witness;
    param_0 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    t <- witness;
    trace_h__MUL__XREG___os_muln <- [];
    trace_h__MUL__XREG___os_muln <-
    (trace_h__MUL__XREG___os_muln ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    ak <- (BArray256.get64 a 0);
    param <- ak;
    param_0 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XREG____mulr_row0 (param, param_0,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XREG___os_muln <-
    (trace_h__MUL__XREG___os_muln ++ tmp__trace);
    trace_h__MUL__XREG___os_muln <-
    (trace_h__MUL__XREG___os_muln ++
    [(Assert, (BArray512.is_init b_result 0 264))]);
    b_t <- b_result;
    t <- result;
    trace_h__MUL__XREG___os_muln <-
    (trace_h__MUL__XREG___os_muln ++ [(Assert, (BArray512.is_init b_t 0 8))]);
    b_r <- (BArray512.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 0 (BArray512.get64 t 0));
    k <- 1;
    while ((k < 32)) {
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 256)))]);
      ak <- (BArray256.get64 a k);
      param_1 <- k;
      b_param <- b_t;
      param_2 <- t;
      param_3 <- ak;
      param_4 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__XREG____mulr_rowk (param_1,
      param_2, b_param, param_3, param_4,
      (BArray256.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++ tmp__trace);
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, (BArray512.is_init b_result_0 0 (8 * ((param_1 + 32) + 1))))]);
      b_t <- b_result_0;
      t <- result_0;
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, (BArray512.is_init b_t (k * 8) 8))]);
      b_r <-
      (BArray512.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r k (BArray512.get64 t k));
      k <- (k + 1);
    }
    inc <- (2 * 32);
    k <- 32;
    while ((k < inc)) {
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, (BArray512.is_init b_t (k * 8) 8))]);
      b_r <-
      (BArray512.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r k (BArray512.get64 t k));
      k <- (k + 1);
    }
    return (r, b_r, trace_h__MUL__XREG___os_muln);
  }
  proc h__MUL__XREG___os_muln_ (r:BArray512.t, b_r:BArray512.t,
                                a:BArray256.t, b_a:BArray256.t,
                                b:BArray256.t, b_b:BArray256.t) : BArray512.t *
                                                                  BArray512.t *
                                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__MUL__XREG___os_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MUL__XREG___os_muln_ <- [];
    trace_h__MUL__XREG___os_muln_ <-
    (trace_h__MUL__XREG___os_muln_ ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XREG___os_muln (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XREG___os_muln_ <-
    (trace_h__MUL__XREG___os_muln_ ++ tmp__trace);
    trace_h__MUL__XREG___os_muln_ <-
    (trace_h__MUL__XREG___os_muln_ ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    r <- r;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XREG___os_muln_);
  }
  proc h__MUL__XREG____sqrr_row0 (a:BArray256.t, b_a:BArray256.t) : BArray512.t *
                                                                    BArray512.t *
                                                                    trace = {
    var aux:W64.t;
    var aux_0:W64.t;
    var aux_1:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_3:bool;
    var aux_5:bool;
    var b_t:BArray512.t;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var t:BArray512.t;
    var j:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__MUL__XREG____sqrr_row0:trace;
    b_t <- witness;
    t <- witness;
    trace_h__MUL__XREG____sqrr_row0 <- [];
    trace_h__MUL__XREG____sqrr_row0 <-
    (trace_h__MUL__XREG____sqrr_row0 ++
    [(Assert, ((2 <= 32) /\ (BArray256.is_init b_a 0 256)))]);
    b_t <- (BArray512.init_arr (W8.of_int 0));
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    ai <- (BArray256.get64 a 0);
    b_t <- (BArray512.set64d b_t 16 (W64.of_int 18446744073709551615));
    b_t <- (BArray512.set64d b_t 8 (W64.of_int 18446744073709551615));
    (aux, aux_0) <- (MULX_64 ai (BArray256.get64 a 1));
    t <- (BArray512.set64 t 2 aux);
    t <- (BArray512.set64 t 1 aux_0);
    j <- 2;
    while ((j < 32)) {
      trace_h__MUL__XREG____sqrr_row0 <-
      (trace_h__MUL__XREG____sqrr_row0 ++
      [(Assert, ((0 <= ((j + 1) * 8)) /\ ((((j + 1) * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____sqrr_row0 <-
      (trace_h__MUL__XREG____sqrr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 256)))]);
      b_t <-
      (BArray512.set64d b_t ((j + 1) * 8) (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (MULX_64 ai (BArray256.get64 a j));
      t <- (BArray512.set64 t (j + 1) aux_1);
      lo <- aux_2;
      trace_h__MUL__XREG____sqrr_row0 <-
      (trace_h__MUL__XREG____sqrr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____sqrr_row0 <-
      (trace_h__MUL__XREG____sqrr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____sqrr_row0 <-
      (trace_h__MUL__XREG____sqrr_row0 ++
      [(Assert, (BArray512.is_init b_t (j * 8) 8))]);
      b_t <-
      (BArray512.set64d b_t (j * 8) (W64.of_int 18446744073709551615));
      (aux_3, aux_4) <- (ADCX_64 (BArray512.get64 t j) lo cf);
      cf <- aux_3;
      t <- (BArray512.set64 t j aux_4);
      j <- (j + 1);
    }
    trace_h__MUL__XREG____sqrr_row0 <-
    (trace_h__MUL__XREG____sqrr_row0 ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____sqrr_row0 <-
    (trace_h__MUL__XREG____sqrr_row0 ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____sqrr_row0 <-
    (trace_h__MUL__XREG____sqrr_row0 ++
    [(Assert, (BArray512.is_init b_t (32 * 8) 8))]);
    b_t <- (BArray512.set64d b_t (32 * 8) (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADCX_64 (BArray512.get64 t 32) _zero cf);
    cf <- aux_5;
    t <- (BArray512.set64 t 32 aux_6);
    return (t, b_t, trace_h__MUL__XREG____sqrr_row0);
  }
  proc h__MUL__XREG____sqrr_rowi (i:int, t:BArray512.t, b_t:BArray512.t,
                                  a:BArray256.t, b_a:BArray256.t) : BArray512.t *
                                                                    BArray512.t *
                                                                    trace = {
    var aux_0:W64.t;
    var aux_2:W64.t;
    var aux_3:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_8:W64.t;
    var aux_10:W64.t;
    var aux:bool;
    var aux_1:bool;
    var aux_5:bool;
    var aux_7:bool;
    var aux_9:bool;
    var inc:int;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var j:int;
    var hi:W64.t;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XREG____sqrr_rowi:trace;
    trace_h__MUL__XREG____sqrr_rowi <- [];
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert,
     ((((1 <= i) /\ (i < (32 - 1))) /\
      (BArray512.is_init b_t 8 (8 * ((i + 32) - 1)))) /\
     (BArray256.is_init b_a 0 256)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
    ai <- (BArray256.get64 a i);
    inc <- (32 - 1);
    j <- (i + 1);
    while ((j < inc)) {
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 256)))]);
      (hi, lo) <- (MULX_64 ai (BArray256.get64 a j));
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert, (BArray512.is_init b_t ((i + j) * 8) 8))]);
      b_t <-
      (BArray512.set64d b_t ((i + j) * 8) (W64.of_int 18446744073709551615));
      (aux, aux_0) <- (ADOX_64 (BArray512.get64 t (i + j)) lo of_0);
      of_0 <- aux;
      t <- (BArray512.set64 t (i + j) aux_0);
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert,
       ((0 <= (((i + j) + 1) * 8)) /\ (((((i + j) + 1) * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert,
       ((0 <= (((i + j) + 1) * 8)) /\ (((((i + j) + 1) * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert, (BArray512.is_init b_t (((i + j) + 1) * 8) 8))]);
      b_t <-
      (BArray512.set64d b_t (((i + j) + 1) * 8)
      (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (ADCX_64 (BArray512.get64 t ((i + j) + 1)) hi cf);
      cf <- aux_1;
      t <- (BArray512.set64 t ((i + j) + 1) aux_2);
      j <- (j + 1);
    }
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 32) * 8)) /\ ((((i + 32) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((32 - 1) * 8)) /\ ((((32 - 1) * 8) + 8) <= 256)))]);
    b_t <-
    (BArray512.set64d b_t ((i + 32) * 8) (W64.of_int 18446744073709551615));
    (aux_3, aux_4) <- (MULX_64 ai (BArray256.get64 a (32 - 1)));
    t <- (BArray512.set64 t (i + 32) aux_3);
    lo <- aux_4;
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert,
     ((0 <= (((i + 32) - 1) * 8)) /\ (((((i + 32) - 1) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert,
     ((0 <= (((i + 32) - 1) * 8)) /\ (((((i + 32) - 1) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, (BArray512.is_init b_t (((i + 32) - 1) * 8) 8))]);
    b_t <-
    (BArray512.set64d b_t (((i + 32) - 1) * 8)
    (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADOX_64 (BArray512.get64 t ((i + 32) - 1)) lo of_0);
    of_0 <- aux_5;
    t <- (BArray512.set64 t ((i + 32) - 1) aux_6);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 32) * 8)) /\ ((((i + 32) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 32) * 8)) /\ ((((i + 32) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, (BArray512.is_init b_t ((i + 32) * 8) 8))]);
    b_t <-
    (BArray512.set64d b_t ((i + 32) * 8) (W64.of_int 18446744073709551615));
    (aux_7, aux_8) <- (ADCX_64 (BArray512.get64 t (i + 32)) _zero cf);
    cf <- aux_7;
    t <- (BArray512.set64 t (i + 32) aux_8);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 32) * 8)) /\ ((((i + 32) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 32) * 8)) /\ ((((i + 32) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, (BArray512.is_init b_t ((i + 32) * 8) 8))]);
    b_t <-
    (BArray512.set64d b_t ((i + 32) * 8) (W64.of_int 18446744073709551615));
    (aux_9, aux_10) <- (ADOX_64 (BArray512.get64 t (i + 32)) _zero of_0);
    of_0 <- aux_9;
    t <- (BArray512.set64 t (i + 32) aux_10);
    return (t, b_t, trace_h__MUL__XREG____sqrr_rowi);
  }
  proc h__MUL__XREG____sqrr_diag (r:BArray512.t, b_r:BArray512.t,
                                  t:BArray512.t, b_t:BArray512.t,
                                  a:BArray256.t, b_a:BArray256.t) : BArray512.t *
                                                                    BArray512.t *
                                                                    trace = {
    var inc:int;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var w:int;
    var x:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XREG____sqrr_diag:trace;
    trace_h__MUL__XREG____sqrr_diag <- [];
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert,
     ((((2 <= 32) /\ (BArray512.is_init b_r 8 432)) /\
      (BArray512.is_init b_t 8 496)) /\
     (BArray256.is_init b_a 0 256)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    ai <- (BArray256.get64 a 0);
    (hi, lo) <- (MULX_64 ai (BArray256.get64 a 0));
    b_r <- (BArray512.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 0 lo);
    w <- 1;
    if (((w + 10) <= (2 * 32))) {
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, (BArray512.is_init b_r (w * 8) 8))]);
      x <- (BArray512.get64 r w);
    } else {
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, (BArray512.is_init b_t (w * 8) 8))]);
      x <- (BArray512.get64 t w);
    }
    (cf, x) <- (ADCX_64 x x cf);
    (of_0, x) <- (ADOX_64 x hi of_0);
    b_r <- (BArray512.set64d b_r 8 (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r 1 x);
    inc <- (32 - 1);
    i <- 1;
    while ((i < inc)) {
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      ai <- (BArray256.get64 a i);
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      (hi, lo) <- (MULX_64 ai (BArray256.get64 a i));
      w <- (2 * i);
      if (((w + 10) <= (2 * 32))) {
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 512)))]);
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, (BArray512.is_init b_r (w * 8) 8))]);
        x <- (BArray512.get64 r w);
      } else {
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 512)))]);
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, (BArray512.is_init b_t (w * 8) 8))]);
        x <- (BArray512.get64 t w);
      }
      (cf, x) <- (ADCX_64 x x cf);
      (of_0, x) <- (ADOX_64 x lo of_0);
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= ((2 * i) * 8)) /\ ((((2 * i) * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r ((2 * i) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r (2 * i) x);
      w <- ((2 * i) + 1);
      if (((w + 10) <= (2 * 32))) {
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 512)))]);
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, (BArray512.is_init b_r (w * 8) 8))]);
        x <- (BArray512.get64 r w);
      } else {
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 512)))]);
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, (BArray512.is_init b_t (w * 8) 8))]);
        x <- (BArray512.get64 t w);
      }
      (cf, x) <- (ADCX_64 x x cf);
      (of_0, x) <- (ADOX_64 x hi of_0);
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert,
       ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (((2 * i) + 1) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r ((2 * i) + 1) x);
      i <- (i + 1);
    }
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert, ((0 <= ((32 - 1) * 8)) /\ ((((32 - 1) * 8) + 8) <= 256)))]);
    ai <- (BArray256.get64 a (32 - 1));
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert, ((0 <= ((32 - 1) * 8)) /\ ((((32 - 1) * 8) + 8) <= 256)))]);
    (hi, lo) <- (MULX_64 ai (BArray256.get64 a (32 - 1)));
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert,
     ((0 <= (((2 * 32) - 2) * 8)) /\ (((((2 * 32) - 2) * 8) + 8) <= 512)))]);
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert, (BArray512.is_init b_t (((2 * 32) - 2) * 8) 8))]);
    x <- (BArray512.get64 t ((2 * 32) - 2));
    (cf, x) <- (ADCX_64 x x cf);
    (of_0, x) <- (ADOX_64 x lo of_0);
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert,
     ((0 <= (((2 * 32) - 2) * 8)) /\ (((((2 * 32) - 2) * 8) + 8) <= 512)))]);
    b_r <-
    (BArray512.set64d b_r (((2 * 32) - 2) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r ((2 * 32) - 2) x);
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert,
     ((0 <= (((2 * 32) - 1) * 8)) /\ (((((2 * 32) - 1) * 8) + 8) <= 512)))]);
    b_r <-
    (BArray512.set64d b_r (((2 * 32) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray512.set64 r ((2 * 32) - 1) hi);
    return (r, b_r, trace_h__MUL__XREG____sqrr_diag);
  }
  proc h__MUL__XREG___os_sqrn (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                               b_a:BArray256.t) : BArray512.t * BArray512.t *
                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var aux_1:BArray512.t;
    var aux_2:BArray512.t;
    var aux_3:BArray512.t;
    var aux_4:BArray512.t;
    var inc:int;
    var inc_0:int;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var param:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var b_t:BArray512.t;
    var t:BArray512.t;
    var w:int;
    var i:int;
    var param_0:int;
    var b_param:BArray512.t;
    var param_1:BArray512.t;
    var param_2:BArray256.t;
    var result_0:BArray512.t;
    var b_result_0:BArray512.t;
    var b_param_0:BArray512.t;
    var param_3:BArray512.t;
    var b_param_1:BArray512.t;
    var param_4:BArray512.t;
    var param_5:BArray256.t;
    var result_1:BArray512.t;
    var b_result_1:BArray512.t;
    var trace_h__MUL__XREG___os_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_t <- witness;
    param <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    t <- witness;
    trace_h__MUL__XREG___os_sqrn <- [];
    trace_h__MUL__XREG___os_sqrn <-
    (trace_h__MUL__XREG___os_sqrn ++
    [(Assert, (BArray256.is_init b_a 0 256))]);
    if ((32 = 1)) {
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 256)))]);
      ai <- (BArray256.get64 a 0);
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 256)))]);
      (hi, lo) <- (MULX_64 ai (BArray256.get64 a 0));
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (0 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r 0 lo);
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++
      [(Assert, ((0 <= (1 * 8)) /\ (((1 * 8) + 8) <= 512)))]);
      b_r <-
      (BArray512.set64d b_r (1 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray512.set64 r 1 hi);
    } else {
      param <- a;
      (aux, aux_0, tmp__trace) <@ h__MUL__XREG____sqrr_row0 (param,
      (BArray256.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++ tmp__trace);
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++
      [(Assert, (BArray512.is_init b_result 8 256))]);
      b_t <- b_result;
      t <- result;
      w <- 1;
      while ((w < 3)) {
        if (((w + 10) <= (2 * 32))) {
          trace_h__MUL__XREG___os_sqrn <-
          (trace_h__MUL__XREG___os_sqrn ++
          [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 512)))]);
          trace_h__MUL__XREG___os_sqrn <-
          (trace_h__MUL__XREG___os_sqrn ++
          [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 512)))]);
          trace_h__MUL__XREG___os_sqrn <-
          (trace_h__MUL__XREG___os_sqrn ++
          [(Assert, (BArray512.is_init b_t (w * 8) 8))]);
          b_r <-
          (BArray512.set64d b_r (w * 8) (W64.of_int 18446744073709551615));
          r <- (BArray512.set64 r w (BArray512.get64 t w));
        } else {
          
        }
        w <- (w + 1);
      }
      inc <- (32 - 1);
      i <- 1;
      while ((i < inc)) {
        param_0 <- i;
        b_param <- b_t;
        param_1 <- t;
        param_2 <- a;
        (aux_1, aux_2, tmp__trace) <@ h__MUL__XREG____sqrr_rowi (param_0,
        param_1, b_param, param_2, (BArray256.init_arr (W8.of_int 255)));
        result_0 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__MUL__XREG___os_sqrn <-
        (trace_h__MUL__XREG___os_sqrn ++ tmp__trace);
        trace_h__MUL__XREG___os_sqrn <-
        (trace_h__MUL__XREG___os_sqrn ++
        [(Assert, (BArray512.is_init b_result_0 8 (8 * (param_0 + 32))))]);
        b_t <- b_result_0;
        t <- result_0;
        inc_0 <- ((2 * i) + 3);
        w <- ((2 * i) + 1);
        while ((w < inc_0)) {
          if (((w + 10) <= (2 * 32))) {
            trace_h__MUL__XREG___os_sqrn <-
            (trace_h__MUL__XREG___os_sqrn ++
            [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 512)))]);
            trace_h__MUL__XREG___os_sqrn <-
            (trace_h__MUL__XREG___os_sqrn ++
            [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 512)))]);
            trace_h__MUL__XREG___os_sqrn <-
            (trace_h__MUL__XREG___os_sqrn ++
            [(Assert, (BArray512.is_init b_t (w * 8) 8))]);
            b_r <-
            (BArray512.set64d b_r (w * 8) (W64.of_int 18446744073709551615));
            r <- (BArray512.set64 r w (BArray512.get64 t w));
          } else {
            
          }
          w <- (w + 1);
        }
        i <- (i + 1);
      }
      b_param_0 <- b_r;
      param_3 <- r;
      b_param_1 <- b_t;
      param_4 <- t;
      param_5 <- a;
      (aux_3, aux_4, tmp__trace) <@ h__MUL__XREG____sqrr_diag (param_3,
      b_param_0, param_4, b_param_1, param_5,
      (BArray256.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++ tmp__trace);
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++
      [(Assert, (BArray512.is_init b_result_1 0 512))]);
      b_r <- (BArray512.init_arr (W8.of_int 255));
      r <- result_1;
    }
    return (r, b_r, trace_h__MUL__XREG___os_sqrn);
  }
  proc h__MUL__XREG___os_sqrn_ (r:BArray512.t, b_r:BArray512.t,
                                a:BArray256.t, b_a:BArray256.t) : BArray512.t *
                                                                  BArray512.t *
                                                                  trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__MUL__XREG___os_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__XREG___os_sqrn_ <- [];
    trace_h__MUL__XREG___os_sqrn_ <-
    (trace_h__MUL__XREG___os_sqrn_ ++
    [(Assert, (BArray256.is_init b_a 0 256))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__XREG___os_sqrn (param, b_param,
    param_0, (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XREG___os_sqrn_ <-
    (trace_h__MUL__XREG___os_sqrn_ ++ tmp__trace);
    trace_h__MUL__XREG___os_sqrn_ <-
    (trace_h__MUL__XREG___os_sqrn_ ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    r <- r;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XREG___os_sqrn_);
  }
  proc h__MUL__XREG____mont_redM (r:BArray256.t, b_r:BArray256.t,
                                  a:BArray512.t, b_a:BArray512.t,
                                  _P_mP:BArray512.t, b__P_mP:BArray512.t,
                                  _U0:W64.t) : BArray256.t * BArray256.t *
                                               trace = {
    var aux_0:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_8:W64.t;
    var aux:bool;
    var aux_1:bool;
    var aux_3:bool;
    var aux_5:bool;
    var aux_7:bool;
    var b_w:BArray512.t;
    var b_s:BArray256.t;
    var i:int;
    var w:BArray512.t;
    var c:W64.t;
    var k:int;
    var m:W64.t;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var s:BArray256.t;
    var x:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var  _12:bool;
    var  _13:W64.t;
    var trace_h__MUL__XREG____mont_redM:trace;
    b_s <- witness;
    b_w <- witness;
    s <- witness;
    w <- witness;
    trace_h__MUL__XREG____mont_redM <- [];
    trace_h__MUL__XREG____mont_redM <-
    (trace_h__MUL__XREG____mont_redM ++
    [(Assert,
     ((BArray512.is_init b_a 0 512) /\ (BArray512.is_init b__P_mP 0 512)))]);
    b_w <- (BArray512.init_arr (W8.of_int 0));
    b_s <- (BArray256.init_arr (W8.of_int 0));
    i <- 0;
    while ((i < 32)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
      b_w <-
      (BArray512.set64d b_w (i * 8) (W64.of_int 18446744073709551615));
      w <- (BArray512.set64 w i (BArray512.get64 a i));
      i <- (i + 1);
    }
    c <- (W64.of_int 0);
    k <- 0;
    while ((k < 32)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray512.is_init b_w (k * 8) 8))]);
      m <- (BArray512.get64 w k);
      m <- (m * _U0);
      (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
      (hi, lo) <- (MULX_64 m (BArray512.get64 _P_mP 0));
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray512.is_init b_w (k * 8) 8))]);
      b_w <-
      (BArray512.set64d b_w (k * 8) (W64.of_int 18446744073709551615));
      (aux, aux_0) <- (ADOX_64 (BArray512.get64 w k) lo of_0);
      of_0 <- aux;
      w <- (BArray512.set64 w k aux_0);
      i <- 1;
      while ((i < 32)) {
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 512)))]);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 512)))]);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, (BArray512.is_init b_w ((k + i) * 8) 8))]);
        b_w <-
        (BArray512.set64d b_w ((k + i) * 8) (W64.of_int 18446744073709551615)
        );
        (aux_1, aux_2) <- (ADCX_64 (BArray512.get64 w (k + i)) hi cf);
        cf <- aux_1;
        w <- (BArray512.set64 w (k + i) aux_2);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 512)))]);
        (hi, lo) <- (MULX_64 m (BArray512.get64 _P_mP i));
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 512)))]);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 512)))]);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, (BArray512.is_init b_w ((k + i) * 8) 8))]);
        b_w <-
        (BArray512.set64d b_w ((k + i) * 8) (W64.of_int 18446744073709551615)
        );
        (aux_3, aux_4) <- (ADOX_64 (BArray512.get64 w (k + i)) lo of_0);
        of_0 <- aux_3;
        w <- (BArray512.set64 w (k + i) aux_4);
        i <- (i + 1);
      }
      (cf, hi) <- (ADCX_64 hi _zero cf);
      (of_0, hi) <- (ADOX_64 hi _zero of_0);
      if ((k = 0)) {
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 8) <= 512)))]);
        (cf, hi) <- (adc_64 hi (BArray512.get64 a 32) false);
      } else {
        ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + 32) * 8)) /\ ((((k + 32) * 8) + 8) <= 512)))]);
        (cf, hi) <- (adc_64 hi (BArray512.get64 a (k + 32)) cf);
      }
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((k + 32) * 8)) /\ ((((k + 32) * 8) + 8) <= 512)))]);
      b_w <-
      (BArray512.set64d b_w ((k + 32) * 8) (W64.of_int 18446744073709551615));
      w <- (BArray512.set64 w (k + 32) hi);
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + 1);
    }
    i <- 0;
    while ((i < 32)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((32 + i) * 8)) /\ ((((32 + i) * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray512.is_init b_w ((32 + i) * 8) 8))]);
      b_s <-
      (BArray256.set64d b_s (i * 8) (W64.of_int 18446744073709551615));
      s <- (BArray256.set64 s i (BArray512.get64 w (32 + i)));
      i <- (i + 1);
    }
    trace_h__MUL__XREG____mont_redM <-
    (trace_h__MUL__XREG____mont_redM ++
    [(Assert, (BArray256.is_init b_s 0 8))]);
    trace_h__MUL__XREG____mont_redM <-
    (trace_h__MUL__XREG____mont_redM ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 8) <= 512)))]);
    b_s <- (BArray256.set64d b_s 0 (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <-
    (adc_64 (BArray256.get64 s 0) (BArray512.get64 _P_mP 32) false);
    cf <- aux_5;
    s <- (BArray256.set64 s 0 aux_6);
    i <- 1;
    while ((i < 32)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray256.is_init b_s (i * 8) 8))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((32 + i) * 8)) /\ ((((32 + i) * 8) + 8) <= 512)))]);
      b_s <-
      (BArray256.set64d b_s (i * 8) (W64.of_int 18446744073709551615));
      (aux_7, aux_8) <-
      (adc_64 (BArray256.get64 s i) (BArray512.get64 _P_mP (32 + i)) cf);
      cf <- aux_7;
      s <- (BArray256.set64 s i aux_8);
      i <- (i + 1);
    }
    ( _8, c) <- (adc_64 c (W64.of_int 0) cf);
    ( _9, cf,  _10,  _11,  _12,  _13) <- (NEG_64 c);
    i <- 0;
    while ((i < 32)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((32 + i) * 8)) /\ ((((32 + i) * 8) + 8) <= 512)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray512.is_init b_w ((32 + i) * 8) 8))]);
      x <- (BArray512.get64 w (32 + i));
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray256.is_init b_s (i * 8) 8))]);
      x <- (cf ? (BArray256.get64 s i) : x);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 256)))]);
      b_r <-
      (BArray256.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray256.set64 r i x);
      i <- (i + 1);
    }
    return (r, b_r, trace_h__MUL__XREG____mont_redM);
  }
  proc h__MUL___muln_ (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                       b_a:BArray256.t, b:BArray256.t, b_b:BArray256.t) : 
  BArray512.t * BArray512.t * trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var aux_1:BArray512.t;
    var aux_2:BArray512.t;
    var aux_3:BArray512.t;
    var aux_4:BArray512.t;
    var aux_5:BArray512.t;
    var aux_6:BArray512.t;
    var aux_7:BArray512.t;
    var aux_8:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var b_param_0:BArray512.t;
    var param_2:BArray512.t;
    var param_3:BArray256.t;
    var param_4:BArray256.t;
    var result_0:BArray512.t;
    var b_result_0:BArray512.t;
    var b_param_1:BArray512.t;
    var param_5:BArray512.t;
    var param_6:BArray256.t;
    var param_7:BArray256.t;
    var result_1:BArray512.t;
    var b_result_1:BArray512.t;
    var b_param_2:BArray512.t;
    var param_8:BArray512.t;
    var param_9:BArray256.t;
    var param_10:BArray256.t;
    var result_2:BArray512.t;
    var b_result_2:BArray512.t;
    var b_param_3:BArray512.t;
    var param_11:BArray512.t;
    var param_12:BArray256.t;
    var param_13:BArray256.t;
    var result_3:BArray512.t;
    var b_result_3:BArray512.t;
    var trace_h__MUL___muln_:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_9 <- witness;
    param_10 <- witness;
    param_11 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    trace_h__MUL___muln_ <- [];
    trace_h__MUL___muln_ <-
    (trace_h__MUL___muln_ ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    if ((((W256.of_int 0) `&` (W256.of_int 3)) = (W256.of_int 3))) {
      if ((32 <= 0)) {
        b_param <- b_r;
        param <- r;
        param_0 <- a;
        param_1 <- b;
        (aux_7, aux_8, tmp__trace) <@ h__MUL__XREG___os_muln_ (param,
        b_param, param_0, (BArray256.init_arr (W8.of_int 255)), param_1,
        (BArray256.init_arr (W8.of_int 255)));
        result <- aux_7;
        b_result <- aux_8;
        trace_h__MUL___muln_ <- (trace_h__MUL___muln_ ++ tmp__trace);
        trace_h__MUL___muln_ <-
        (trace_h__MUL___muln_ ++
        [(Assert, (BArray512.is_init b_result 0 512))]);
        r <- result;
      } else {
        if ((32 <= 64)) {
          b_param_0 <- b_r;
          param_2 <- r;
          param_3 <- a;
          param_4 <- b;
          (aux_5, aux_6, tmp__trace) <@ h__MUL__XUNR___os_muln_ (param_2,
          b_param_0, param_3, (BArray256.init_arr (W8.of_int 255)), param_4,
          (BArray256.init_arr (W8.of_int 255)));
          result_0 <- aux_5;
          b_result_0 <- aux_6;
          trace_h__MUL___muln_ <- (trace_h__MUL___muln_ ++ tmp__trace);
          trace_h__MUL___muln_ <-
          (trace_h__MUL___muln_ ++
          [(Assert, (BArray512.is_init b_result_0 0 512))]);
          r <- result_0;
        } else {
          b_param_1 <- b_r;
          param_5 <- r;
          param_6 <- a;
          param_7 <- b;
          (aux_3, aux_4, tmp__trace) <@ h__MUL__XLOOP___os_muln_ (param_5,
          b_param_1, param_6, (BArray256.init_arr (W8.of_int 255)), param_7,
          (BArray256.init_arr (W8.of_int 255)));
          result_1 <- aux_3;
          b_result_1 <- aux_4;
          trace_h__MUL___muln_ <- (trace_h__MUL___muln_ ++ tmp__trace);
          trace_h__MUL___muln_ <-
          (trace_h__MUL___muln_ ++
          [(Assert, (BArray512.is_init b_result_1 0 512))]);
          r <- result_1;
        }
      }
    } else {
      if ((32 <= 64)) {
        b_param_2 <- b_r;
        param_8 <- r;
        param_9 <- a;
        param_10 <- b;
        (aux_1, aux_2, tmp__trace) <@ h__MUL__UNR___ps_muln_ (param_8,
        b_param_2, param_9, (BArray256.init_arr (W8.of_int 255)), param_10,
        (BArray256.init_arr (W8.of_int 255)));
        result_2 <- aux_1;
        b_result_2 <- aux_2;
        trace_h__MUL___muln_ <- (trace_h__MUL___muln_ ++ tmp__trace);
        trace_h__MUL___muln_ <-
        (trace_h__MUL___muln_ ++
        [(Assert, (BArray512.is_init b_result_2 0 512))]);
        r <- result_2;
      } else {
        b_param_3 <- b_r;
        param_11 <- r;
        param_12 <- a;
        param_13 <- b;
        (aux, aux_0, tmp__trace) <@ h__MUL__LOOP___os_muln_ (param_11,
        b_param_3, param_12, (BArray256.init_arr (W8.of_int 255)), param_13,
        (BArray256.init_arr (W8.of_int 255)));
        result_3 <- aux;
        b_result_3 <- aux_0;
        trace_h__MUL___muln_ <- (trace_h__MUL___muln_ ++ tmp__trace);
        trace_h__MUL___muln_ <-
        (trace_h__MUL___muln_ ++
        [(Assert, (BArray512.is_init b_result_3 0 512))]);
        r <- result_3;
      }
    }
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL___muln_);
  }
  proc h__MUL___sqrn_ (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                       b_a:BArray256.t) : BArray512.t * BArray512.t * trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var aux_1:BArray512.t;
    var aux_2:BArray512.t;
    var aux_3:BArray512.t;
    var aux_4:BArray512.t;
    var aux_5:BArray512.t;
    var aux_6:BArray512.t;
    var aux_7:BArray512.t;
    var aux_8:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var b_param_0:BArray512.t;
    var param_1:BArray512.t;
    var param_2:BArray256.t;
    var result_0:BArray512.t;
    var b_result_0:BArray512.t;
    var b_param_1:BArray512.t;
    var param_3:BArray512.t;
    var param_4:BArray256.t;
    var result_1:BArray512.t;
    var b_result_1:BArray512.t;
    var b_param_2:BArray512.t;
    var param_5:BArray512.t;
    var param_6:BArray256.t;
    var result_2:BArray512.t;
    var b_result_2:BArray512.t;
    var b_param_3:BArray512.t;
    var param_7:BArray512.t;
    var param_8:BArray256.t;
    var result_3:BArray512.t;
    var b_result_3:BArray512.t;
    var trace_h__MUL___sqrn_:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    trace_h__MUL___sqrn_ <- [];
    trace_h__MUL___sqrn_ <-
    (trace_h__MUL___sqrn_ ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    if ((((W256.of_int 0) `&` (W256.of_int 3)) = (W256.of_int 3))) {
      if ((32 <= 0)) {
        b_param <- b_r;
        param <- r;
        param_0 <- a;
        (aux_7, aux_8, tmp__trace) <@ h__MUL__XREG___os_sqrn_ (param,
        b_param, param_0, (BArray256.init_arr (W8.of_int 255)));
        result <- aux_7;
        b_result <- aux_8;
        trace_h__MUL___sqrn_ <- (trace_h__MUL___sqrn_ ++ tmp__trace);
        trace_h__MUL___sqrn_ <-
        (trace_h__MUL___sqrn_ ++
        [(Assert, (BArray512.is_init b_result 0 512))]);
        r <- result;
      } else {
        if ((32 <= 64)) {
          b_param_0 <- b_r;
          param_1 <- r;
          param_2 <- a;
          (aux_5, aux_6, tmp__trace) <@ h__MUL__XUNR___os_sqrn_ (param_1,
          b_param_0, param_2, (BArray256.init_arr (W8.of_int 255)));
          result_0 <- aux_5;
          b_result_0 <- aux_6;
          trace_h__MUL___sqrn_ <- (trace_h__MUL___sqrn_ ++ tmp__trace);
          trace_h__MUL___sqrn_ <-
          (trace_h__MUL___sqrn_ ++
          [(Assert, (BArray512.is_init b_result_0 0 512))]);
          r <- result_0;
        } else {
          b_param_1 <- b_r;
          param_3 <- r;
          param_4 <- a;
          (aux_3, aux_4, tmp__trace) <@ h__MUL__XLOOP___os_sqrn_ (param_3,
          b_param_1, param_4, (BArray256.init_arr (W8.of_int 255)));
          result_1 <- aux_3;
          b_result_1 <- aux_4;
          trace_h__MUL___sqrn_ <- (trace_h__MUL___sqrn_ ++ tmp__trace);
          trace_h__MUL___sqrn_ <-
          (trace_h__MUL___sqrn_ ++
          [(Assert, (BArray512.is_init b_result_1 0 512))]);
          r <- result_1;
        }
      }
    } else {
      if ((32 <= 64)) {
        b_param_2 <- b_r;
        param_5 <- r;
        param_6 <- a;
        (aux_1, aux_2, tmp__trace) <@ h__MUL__UNR___ps_sqrn_ (param_5,
        b_param_2, param_6, (BArray256.init_arr (W8.of_int 255)));
        result_2 <- aux_1;
        b_result_2 <- aux_2;
        trace_h__MUL___sqrn_ <- (trace_h__MUL___sqrn_ ++ tmp__trace);
        trace_h__MUL___sqrn_ <-
        (trace_h__MUL___sqrn_ ++
        [(Assert, (BArray512.is_init b_result_2 0 512))]);
        r <- result_2;
      } else {
        b_param_3 <- b_r;
        param_7 <- r;
        param_8 <- a;
        (aux, aux_0, tmp__trace) <@ h__MUL__LOOP___os_sqrn_ (param_7,
        b_param_3, param_8, (BArray256.init_arr (W8.of_int 255)));
        result_3 <- aux;
        b_result_3 <- aux_0;
        trace_h__MUL___sqrn_ <- (trace_h__MUL___sqrn_ ++ tmp__trace);
        trace_h__MUL___sqrn_ <-
        (trace_h__MUL___sqrn_ ++
        [(Assert, (BArray512.is_init b_result_3 0 512))]);
        r <- result_3;
      }
    }
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL___sqrn_);
  }
  proc h__MUL____mont_redM (r:BArray256.t, b_r:BArray256.t, a:BArray512.t,
                            b_a:BArray512.t, _P_mP:BArray512.t,
                            b__P_mP:BArray512.t, _U0:W64.t) : BArray256.t *
                                                              BArray256.t *
                                                              trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var aux_3:BArray256.t;
    var aux_4:BArray256.t;
    var aux_5:BArray256.t;
    var aux_6:BArray256.t;
    var aux_7:BArray256.t;
    var aux_8:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray512.t;
    var param_1:BArray512.t;
    var param_2:W64.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var b_param_0:BArray256.t;
    var param_3:BArray256.t;
    var param_4:BArray512.t;
    var param_5:BArray512.t;
    var param_6:W64.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var b_param_1:BArray256.t;
    var param_7:BArray256.t;
    var param_8:BArray512.t;
    var param_9:BArray512.t;
    var param_10:W64.t;
    var result_1:BArray256.t;
    var b_result_1:BArray256.t;
    var b_param_2:BArray256.t;
    var param_11:BArray256.t;
    var param_12:BArray512.t;
    var param_13:BArray512.t;
    var param_14:W64.t;
    var result_2:BArray256.t;
    var b_result_2:BArray256.t;
    var b_param_3:BArray256.t;
    var param_15:BArray256.t;
    var param_16:BArray512.t;
    var param_17:BArray512.t;
    var param_18:W64.t;
    var result_3:BArray256.t;
    var b_result_3:BArray256.t;
    var trace_h__MUL____mont_redM:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_9 <- witness;
    param_11 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    param_15 <- witness;
    param_16 <- witness;
    param_17 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    trace_h__MUL____mont_redM <- [];
    trace_h__MUL____mont_redM <-
    (trace_h__MUL____mont_redM ++
    [(Assert,
     ((BArray512.is_init b_a 0 512) /\ (BArray512.is_init b__P_mP 0 512)))]);
    if ((((W256.of_int 0) `&` (W256.of_int 3)) = (W256.of_int 3))) {
      if ((32 <= 0)) {
        b_param <- b_r;
        param <- r;
        param_0 <- a;
        param_1 <- _P_mP;
        param_2 <- _U0;
        (aux_7, aux_8, tmp__trace) <@ h__MUL__XREG____mont_redM (param,
        b_param, param_0, (BArray512.init_arr (W8.of_int 255)), param_1,
        (BArray512.init_arr (W8.of_int 255)), param_2);
        result <- aux_7;
        b_result <- aux_8;
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++ tmp__trace);
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++
        [(Assert, (BArray256.is_init b_result 0 256))]);
        r <- result;
      } else {
        if ((32 <= 64)) {
          b_param_0 <- b_r;
          param_3 <- r;
          param_4 <- a;
          param_5 <- _P_mP;
          param_6 <- _U0;
          (aux_5, aux_6, tmp__trace) <@ h__MUL__XUNR____mont_redM (param_3,
          b_param_0, param_4, (BArray512.init_arr (W8.of_int 255)), param_5,
          (BArray512.init_arr (W8.of_int 255)), param_6);
          result_0 <- aux_5;
          b_result_0 <- aux_6;
          trace_h__MUL____mont_redM <-
          (trace_h__MUL____mont_redM ++ tmp__trace);
          trace_h__MUL____mont_redM <-
          (trace_h__MUL____mont_redM ++
          [(Assert, (BArray256.is_init b_result_0 0 256))]);
          r <- result_0;
        } else {
          b_param_1 <- b_r;
          param_7 <- r;
          param_8 <- a;
          param_9 <- _P_mP;
          param_10 <- _U0;
          (aux_3, aux_4, tmp__trace) <@ h__MUL__XLOOP____mont_redM (param_7,
          b_param_1, param_8, (BArray512.init_arr (W8.of_int 255)), param_9,
          (BArray512.init_arr (W8.of_int 255)), param_10);
          result_1 <- aux_3;
          b_result_1 <- aux_4;
          trace_h__MUL____mont_redM <-
          (trace_h__MUL____mont_redM ++ tmp__trace);
          trace_h__MUL____mont_redM <-
          (trace_h__MUL____mont_redM ++
          [(Assert, (BArray256.is_init b_result_1 0 256))]);
          r <- result_1;
        }
      }
    } else {
      if ((32 <= 64)) {
        b_param_2 <- b_r;
        param_11 <- r;
        param_12 <- a;
        param_13 <- _P_mP;
        param_14 <- _U0;
        (aux_1, aux_2, tmp__trace) <@ h__MUL__UNR____mont_redM (param_11,
        b_param_2, param_12, (BArray512.init_arr (W8.of_int 255)), param_13,
        (BArray512.init_arr (W8.of_int 255)), param_14);
        result_2 <- aux_1;
        b_result_2 <- aux_2;
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++ tmp__trace);
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++
        [(Assert, (BArray256.is_init b_result_2 0 256))]);
        r <- result_2;
      } else {
        b_param_3 <- b_r;
        param_15 <- r;
        param_16 <- a;
        param_17 <- _P_mP;
        param_18 <- _U0;
        (aux, aux_0, tmp__trace) <@ h__MUL__LOOP____mont_redM (param_15,
        b_param_3, param_16, (BArray512.init_arr (W8.of_int 255)), param_17,
        (BArray512.init_arr (W8.of_int 255)), param_18);
        result_3 <- aux;
        b_result_3 <- aux_0;
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++ tmp__trace);
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++
        [(Assert, (BArray256.is_init b_result_3 0 256))]);
        r <- result_3;
      }
    }
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL____mont_redM);
  }
  proc h__FPM__fun_muln (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                         b_a:BArray256.t, b:BArray256.t, b_b:BArray256.t) : 
  BArray512.t * BArray512.t * trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__FPM__fun_muln:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPM__fun_muln <- [];
    trace_h__FPM__fun_muln <-
    (trace_h__FPM__fun_muln ++
    [(Assert,
     ((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL___muln_ (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__fun_muln <- (trace_h__FPM__fun_muln ++ tmp__trace);
    trace_h__FPM__fun_muln <-
    (trace_h__FPM__fun_muln ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__fun_muln);
  }
  proc h__FPM__fun_sqrn (r:BArray512.t, b_r:BArray512.t, a:BArray256.t,
                         b_a:BArray256.t) : BArray512.t * BArray512.t * trace = {
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var trace_h__FPM__fun_sqrn:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__FPM__fun_sqrn <- [];
    trace_h__FPM__fun_sqrn <-
    (trace_h__FPM__fun_sqrn ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL___sqrn_ (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__fun_sqrn <- (trace_h__FPM__fun_sqrn ++ tmp__trace);
    trace_h__FPM__fun_sqrn <-
    (trace_h__FPM__fun_sqrn ++
    [(Assert, (BArray512.is_init b_result 0 512))]);
    r <- result;
    b_r <- (BArray512.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__fun_sqrn);
  }
  proc h__FPM___redM (r:BArray256.t, b_r:BArray256.t, a:BArray512.t,
                      b_a:BArray512.t, ctx:BArray1032.t, b_ctx:BArray1032.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var t:W64.t;
    var _u0:W64.t;
    var b_PmP:BArray512.t;
    var pmP:BArray512.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray512.t;
    var b_param_0:BArray512.t;
    var param_1:BArray512.t;
    var param_2:W64.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__FPM___redM:trace;
    pmP <- witness;
    b_PmP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPM___redM <- [];
    trace_h__FPM___redM <-
    (trace_h__FPM___redM ++
    [(Assert,
     ((BArray512.is_init b_a 0 512) /\ (BArray1032.is_init b_ctx 0 1032)))]);
    trace_h__FPM___redM <-
    (trace_h__FPM___redM ++
    [(Assert, ((0 <= (128 * 8)) /\ (((128 * 8) + 8) <= 1032)))]);
    t <- (BArray1032.get64 ctx 128);
    _u0 <- t;
    trace_h__FPM___redM <-
    (trace_h__FPM___redM ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 512) <= 1032)))]);
    b_PmP <- (SBArray1032_512.get_sub64 b_ctx 0);
    pmP <- (SBArray1032_512.get_sub64 ctx 0);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    b_param_0 <- b_PmP;
    param_1 <- pmP;
    param_2 <- _u0;
    (aux, aux_0, tmp__trace) <@ h__MUL____mont_redM (param, b_param, 
    param_0, (BArray512.init_arr (W8.of_int 255)), param_1, b_param_0,
    param_2);
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___redM <- (trace_h__FPM___redM ++ tmp__trace);
    trace_h__FPM___redM <-
    (trace_h__FPM___redM ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM___redM);
  }
  proc h__FPM___redM_ (r:BArray256.t, b_r:BArray256.t, a:BArray512.t,
                       b_a:BArray512.t, ctx:BArray1032.t, b_ctx:BArray1032.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray512.t;
    var param_1:BArray1032.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__FPM___redM_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPM___redM_ <- [];
    trace_h__FPM___redM_ <-
    (trace_h__FPM___redM_ ++
    [(Assert,
     ((BArray512.is_init b_a 0 512) /\ (BArray1032.is_init b_ctx 0 1032)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    ctx <- ctx;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM___redM (param, b_param, param_0,
    (BArray512.init_arr (W8.of_int 255)), param_1,
    (BArray1032.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___redM_ <- (trace_h__FPM___redM_ ++ tmp__trace);
    trace_h__FPM___redM_ <-
    (trace_h__FPM___redM_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM___redM_);
  }
  proc h__FPM___fromM_ (a:BArray256.t, b_a:BArray256.t, ctx:BArray1032.t,
                        b_ctx:BArray1032.t) : BArray256.t * BArray256.t *
                                              trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var aux_3:BArray256.t;
    var aux_4:BArray256.t;
    var b__tmp:BArray512.t;
    var b_tmp2:BArray256.t;
    var tmp2:BArray256.t;
    var _tmp:BArray512.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var b_param_0:BArray256.t;
    var param_1:BArray256.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var b_tmp:BArray512.t;
    var tmp:BArray512.t;
    var param_2:BArray256.t;
    var b_param_1:BArray512.t;
    var param_3:BArray512.t;
    var param_4:BArray1032.t;
    var result_1:BArray256.t;
    var b_result_1:BArray256.t;
    var trace_h__FPM___fromM_:trace;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_tmp <- witness;
    b_tmp2 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    tmp <- witness;
    tmp2 <- witness;
    trace_h__FPM___fromM_ <- [];
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++ [(Assert, (BArray1032.is_init b_ctx 0 1032))]);
    b__tmp <- (BArray512.init_arr (W8.of_int 0));
    b_tmp2 <- (SBArray512_256.get_sub64 b__tmp 0);
    tmp2 <- (SBArray512_256.get_sub64 _tmp 0);
    b_param <- b_tmp2;
    param <- tmp2;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___fromM_ <- (trace_h__FPM___fromM_ ++ tmp__trace);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    tmp2 <- result;
    b__tmp <-
    (SBArray512_256.set_sub64 b__tmp 0 (BArray256.init_arr (W8.of_int 255)));
    _tmp <- (SBArray512_256.set_sub64 _tmp 0 tmp2);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 256) <= 512)))]);
    b_tmp2 <- (SBArray512_256.get_sub64 b__tmp 32);
    tmp2 <- (SBArray512_256.get_sub64 _tmp 32);
    b_param_0 <- b_tmp2;
    param_1 <- tmp2;
    (aux_1, aux_2, tmp__trace) <@ h__BN___set0_ (param_1, b_param_0);
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM___fromM_ <- (trace_h__FPM___fromM_ ++ tmp__trace);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++
    [(Assert, (BArray256.is_init b_result_0 0 256))]);
    tmp2 <- result_0;
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 256) <= 512)))]);
    b__tmp <-
    (SBArray512_256.set_sub64 b__tmp 32 (BArray256.init_arr (W8.of_int 255)));
    _tmp <- (SBArray512_256.set_sub64 _tmp 32 tmp2);
    b_tmp <- b__tmp;
    tmp <- _tmp;
    param_2 <- a;
    b_param_1 <- b_tmp;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_3, aux_4, tmp__trace) <@ h__FPM___redM_ (param_2,
    (BArray256.init_arr (W8.of_int 255)), param_3, b_param_1, param_4,
    (BArray1032.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_h__FPM___fromM_ <- (trace_h__FPM___fromM_ ++ tmp__trace);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++
    [(Assert, (BArray256.is_init b_result_1 0 256))]);
    a <- result_1;
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM___fromM_);
  }
  proc h__FPM__fun_red (r:BArray256.t, b_r:BArray256.t, a:BArray512.t,
                        b_a:BArray512.t, ctx:BArray1032.t, b_ctx:BArray1032.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray512.t;
    var param_1:BArray1032.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__FPM__fun_red:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPM__fun_red <- [];
    trace_h__FPM__fun_red <-
    (trace_h__FPM__fun_red ++
    [(Assert,
     ((BArray512.is_init b_a 0 512) /\ (BArray1032.is_init b_ctx 0 1032)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM___redM_ (param, b_param, param_0,
    (BArray512.init_arr (W8.of_int 255)), param_1,
    (BArray1032.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__fun_red <- (trace_h__FPM__fun_red ++ tmp__trace);
    trace_h__FPM__fun_red <-
    (trace_h__FPM__fun_red ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__fun_red);
  }
  proc h__FPM___addm_ (r:BArray256.t, b_r:BArray256.t, a:BArray256.t,
                       b_a:BArray256.t, b:BArray256.t, b_b:BArray256.t,
                       ctx:BArray1032.t, b_ctx:BArray1032.t) : BArray256.t *
                                                               BArray256.t *
                                                               trace = {
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var aux_3:BArray256.t;
    var aux:bool;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var result:bool;
    var result_0:BArray256.t;
    var b_result:BArray256.t;
    var cf:bool;
    var lastbit:W64.t;
    var b_tmp:BArray256.t;
    var tmp:BArray256.t;
    var param_2:BArray256.t;
    var b_param_0:BArray256.t;
    var param_3:BArray256.t;
    var param_4:W64.t;
    var result_1:BArray256.t;
    var b_result_0:BArray256.t;
    var  _0:bool;
    var trace_h__FPM___addm_:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    result_0 <- witness;
    result_1 <- witness;
    tmp <- witness;
    trace_h__FPM___addm_ <- [];
    trace_h__FPM___addm_ <-
    (trace_h__FPM___addm_ ++
    [(Assert,
     (((BArray256.is_init b_a 0 256) /\ (BArray256.is_init b_b 0 256)) /\
     (BArray1032.is_init b_ctx 256 256)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___add_ (param, b_param, 
    param_0, (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__FPM___addm_ <- (trace_h__FPM___addm_ ++ tmp__trace);
    trace_h__FPM___addm_ <-
    (trace_h__FPM___addm_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    cf <- result;
    r <- result_0;
    lastbit <- (W64.of_int 0);
    ( _0, lastbit) <- (adc_64 lastbit (W64.of_int 0) cf);
    trace_h__FPM___addm_ <-
    (trace_h__FPM___addm_ ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 256) <= 1032)))]);
    b_tmp <- (SBArray1032_256.get_sub64 b_ctx 32);
    tmp <- (SBArray1032_256.get_sub64 ctx 32);
    param_2 <- r;
    b_param_0 <- b_tmp;
    param_3 <- tmp;
    param_4 <- lastbit;
    (aux_2, aux_3, tmp__trace) <@ h__BN___cminusP_ (param_2,
    (BArray256.init_arr (W8.of_int 255)), param_3, b_param_0, param_4);
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__FPM___addm_ <- (trace_h__FPM___addm_ ++ tmp__trace);
    trace_h__FPM___addm_ <-
    (trace_h__FPM___addm_ ++
    [(Assert, (BArray256.is_init b_result_0 0 256))]);
    r <- result_1;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM___addm_);
  }
  proc h__FPM___mulmU_ (a:BArray256.t, b_a:BArray256.t, b:BArray256.t,
                        b_b:BArray256.t, ctx:BArray1032.t, b_ctx:BArray1032.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b__tmp:BArray512.t;
    var _a:BArray256.t;
    var _ctx:BArray1032.t;
    var b_tmp:BArray512.t;
    var tmp:BArray512.t;
    var _tmp:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var param_1:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var param_2:BArray256.t;
    var param_3:BArray512.t;
    var param_4:BArray1032.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var trace_h__FPM___mulmU_:trace;
    _a <- witness;
    _ctx <- witness;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    tmp <- witness;
    trace_h__FPM___mulmU_ <- [];
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray256.is_init b_b 0 256))]);
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray1032.is_init b_ctx 0 1032))]);
    b__tmp <- (BArray512.init_arr (W8.of_int 0));
    _a <- a;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__FPM__fun_muln (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___mulmU_ <- (trace_h__FPM___mulmU_ ++ tmp__trace);
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray512.is_init b_result 0 512))]);
    tmp <- result;
    a <- _a;
    ctx <- _ctx;
    param_2 <- a;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM__fun_red (param_2,
    (BArray256.init_arr (W8.of_int 255)), param_3,
    (BArray512.init_arr (W8.of_int 255)), param_4,
    (BArray1032.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM___mulmU_ <- (trace_h__FPM___mulmU_ ++ tmp__trace);
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++
    [(Assert, (BArray256.is_init b_result_0 0 256))]);
    a <- result_0;
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM___mulmU_);
  }
  proc h__FPM___sqrmU_ (a:BArray256.t, b_a:BArray256.t, ctx:BArray1032.t,
                        b_ctx:BArray1032.t) : BArray256.t * BArray256.t *
                                              trace = {
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var aux:BArray512.t;
    var aux_0:BArray512.t;
    var b__tmp:BArray512.t;
    var _a:BArray256.t;
    var _ctx:BArray1032.t;
    var b_tmp:BArray512.t;
    var tmp:BArray512.t;
    var _tmp:BArray512.t;
    var b_param:BArray512.t;
    var param:BArray512.t;
    var param_0:BArray256.t;
    var result:BArray512.t;
    var b_result:BArray512.t;
    var param_1:BArray256.t;
    var param_2:BArray512.t;
    var param_3:BArray1032.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var trace_h__FPM___sqrmU_:trace;
    _a <- witness;
    _ctx <- witness;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    result <- witness;
    result_0 <- witness;
    tmp <- witness;
    trace_h__FPM___sqrmU_ <- [];
    trace_h__FPM___sqrmU_ <-
    (trace_h__FPM___sqrmU_ ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    trace_h__FPM___sqrmU_ <-
    (trace_h__FPM___sqrmU_ ++ [(Assert, (BArray1032.is_init b_ctx 0 1032))]);
    b__tmp <- (BArray512.init_arr (W8.of_int 0));
    _a <- a;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__FPM__fun_sqrn (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___sqrmU_ <- (trace_h__FPM___sqrmU_ ++ tmp__trace);
    trace_h__FPM___sqrmU_ <-
    (trace_h__FPM___sqrmU_ ++ [(Assert, (BArray512.is_init b_result 0 512))]);
    tmp <- result;
    a <- _a;
    ctx <- _ctx;
    param_1 <- a;
    param_2 <- tmp;
    param_3 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM__fun_red (param_1,
    (BArray256.init_arr (W8.of_int 255)), param_2,
    (BArray512.init_arr (W8.of_int 255)), param_3,
    (BArray1032.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM___sqrmU_ <- (trace_h__FPM___sqrmU_ ++ tmp__trace);
    trace_h__FPM___sqrmU_ <-
    (trace_h__FPM___sqrmU_ ++
    [(Assert, (BArray256.is_init b_result_0 0 256))]);
    a <- result_0;
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM___sqrmU_);
  }
  proc h__FPM__fun_mulU (a:BArray256.t, b_a:BArray256.t, b:BArray256.t,
                         b_b:BArray256.t, ctx:BArray1032.t,
                         b_ctx:BArray1032.t) : BArray256.t * BArray256.t *
                                               trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:BArray1032.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__FPM__fun_mulU:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPM__fun_mulU <- [];
    trace_h__FPM__fun_mulU <-
    (trace_h__FPM__fun_mulU ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    trace_h__FPM__fun_mulU <-
    (trace_h__FPM__fun_mulU ++ [(Assert, (BArray256.is_init b_b 0 256))]);
    trace_h__FPM__fun_mulU <-
    (trace_h__FPM__fun_mulU ++ [(Assert, (BArray1032.is_init b_ctx 0 1032))]);
    param <- a;
    param_0 <- b;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM___mulmU_ (param,
    (BArray256.init_arr (W8.of_int 255)), param_0,
    (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray1032.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__fun_mulU <- (trace_h__FPM__fun_mulU ++ tmp__trace);
    trace_h__FPM__fun_mulU <-
    (trace_h__FPM__fun_mulU ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    a <- result;
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM__fun_mulU);
  }
  proc h__FPM__fun_sqrU (a:BArray256.t, b_a:BArray256.t, ctx:BArray1032.t,
                         b_ctx:BArray1032.t) : BArray256.t * BArray256.t *
                                               trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray1032.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__FPM__fun_sqrU:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__FPM__fun_sqrU <- [];
    trace_h__FPM__fun_sqrU <-
    (trace_h__FPM__fun_sqrU ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    trace_h__FPM__fun_sqrU <-
    (trace_h__FPM__fun_sqrU ++ [(Assert, (BArray1032.is_init b_ctx 0 1032))]);
    param <- a;
    param_0 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM___sqrmU_ (param,
    (BArray256.init_arr (W8.of_int 255)), param_0,
    (BArray1032.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__fun_sqrU <- (trace_h__FPM__fun_sqrU ++ tmp__trace);
    trace_h__FPM__fun_sqrU <-
    (trace_h__FPM__fun_sqrU ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    a <- result;
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM__fun_sqrU);
  }
  proc h__FPM___toM_ (a:BArray256.t, b_a:BArray256.t, ctx:BArray1032.t,
                      b_ctx:BArray1032.t) : BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_R2:BArray256.t;
    var r2:BArray256.t;
    var param:BArray256.t;
    var b_param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:BArray1032.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_h__FPM___toM_:trace;
    r2 <- witness;
    b_R2 <- witness;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPM___toM_ <- [];
    trace_h__FPM___toM_ <-
    (trace_h__FPM___toM_ ++ [(Assert, (BArray256.is_init b_a 0 256))]);
    trace_h__FPM___toM_ <-
    (trace_h__FPM___toM_ ++ [(Assert, (BArray1032.is_init b_ctx 0 1032))]);
    trace_h__FPM___toM_ <-
    (trace_h__FPM___toM_ ++
    [(Assert, ((0 <= (96 * 8)) /\ (((96 * 8) + 256) <= 1032)))]);
    b_R2 <- (SBArray1032_256.get_sub64 b_ctx 96);
    r2 <- (SBArray1032_256.get_sub64 ctx 96);
    param <- a;
    b_param <- b_R2;
    param_0 <- r2;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM___mulmU_ (param,
    (BArray256.init_arr (W8.of_int 255)), param_0, b_param, param_1,
    (BArray1032.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___toM_ <- (trace_h__FPM___toM_ ++ tmp__trace);
    trace_h__FPM___toM_ <-
    (trace_h__FPM___toM_ ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    a <- result;
    a <- a;
    b_a <- (BArray256.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM___toM_);
  }
  proc h__FPM___ctx_init_ (ctx:BArray1032.t, b_ctx:BArray1032.t,
                           p:BArray256.t, b_P:BArray256.t) : BArray1032.t *
                                                             BArray1032.t *
                                                             trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_2:BArray256.t;
    var aux_3:BArray256.t;
    var aux_4:BArray256.t;
    var aux_5:BArray256.t;
    var aux_6:BArray256.t;
    var aux_7:BArray256.t;
    var aux_8:BArray256.t;
    var aux_9:BArray256.t;
    var aux_10:BArray256.t;
    var aux_11:BArray256.t;
    var aux_12:BArray256.t;
    var aux_13:BArray256.t;
    var aux_14:BArray256.t;
    var aux_15:BArray256.t;
    var aux_16:BArray256.t;
    var aux_17:BArray256.t;
    var aux_1:bool;
    var b__x:BArray256.t;
    var b__y:BArray256.t;
    var b_t:BArray256.t;
    var t:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var b_param_0:BArray256.t;
    var param_1:BArray256.t;
    var param_2:BArray256.t;
    var result_0:bool;
    var result_1:BArray256.t;
    var b_result_0:BArray256.t;
    var p0:W64.t;
    var inv:W64.t;
    var j:int;
    var d:W64.t;
    var u0:W64.t;
    var b_x:BArray256.t;
    var x:BArray256.t;
    var _x:BArray256.t;
    var b_param_1:BArray256.t;
    var param_3:BArray256.t;
    var result_2:BArray256.t;
    var b_result_1:BArray256.t;
    var i:W64.t;
    var _i:W64.t;
    var b_y:BArray256.t;
    var y:BArray256.t;
    var _y:BArray256.t;
    var b_param_2:BArray256.t;
    var param_4:BArray256.t;
    var param_5:BArray256.t;
    var param_6:BArray256.t;
    var b_param_3:BArray1032.t;
    var param_7:BArray1032.t;
    var result_3:BArray256.t;
    var b_result_2:BArray256.t;
    var param_8:BArray256.t;
    var param_9:BArray256.t;
    var param_10:BArray256.t;
    var b_param_4:BArray1032.t;
    var param_11:BArray1032.t;
    var result_4:BArray256.t;
    var b_result_3:BArray256.t;
    var b_param_5:BArray256.t;
    var param_12:BArray256.t;
    var param_13:BArray256.t;
    var result_5:BArray256.t;
    var b_result_4:BArray256.t;
    var b_param_6:BArray256.t;
    var param_14:BArray256.t;
    var param_15:BArray256.t;
    var param_16:BArray256.t;
    var b_param_7:BArray1032.t;
    var param_17:BArray1032.t;
    var result_6:BArray256.t;
    var b_result_5:BArray256.t;
    var param_18:BArray256.t;
    var param_19:BArray256.t;
    var param_20:BArray256.t;
    var b_param_8:BArray1032.t;
    var param_21:BArray1032.t;
    var result_7:BArray256.t;
    var b_result_6:BArray256.t;
    var b_param_9:BArray256.t;
    var param_22:BArray256.t;
    var param_23:BArray256.t;
    var result_8:BArray256.t;
    var b_result_7:BArray256.t;
    var trace_h__FPM___ctx_init_:trace;
    _x <- witness;
    _y <- witness;
    b__x <- witness;
    b__y <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    b_param_7 <- witness;
    b_param_8 <- witness;
    b_param_9 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_result_5 <- witness;
    b_result_6 <- witness;
    b_result_7 <- witness;
    b_t <- witness;
    b_x <- witness;
    b_y <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_9 <- witness;
    param_10 <- witness;
    param_11 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    param_14 <- witness;
    param_15 <- witness;
    param_16 <- witness;
    param_17 <- witness;
    param_18 <- witness;
    param_19 <- witness;
    param_20 <- witness;
    param_21 <- witness;
    param_22 <- witness;
    param_23 <- witness;
    result <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_4 <- witness;
    result_5 <- witness;
    result_6 <- witness;
    result_7 <- witness;
    result_8 <- witness;
    t <- witness;
    x <- witness;
    y <- witness;
    trace_h__FPM___ctx_init_ <- [];
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++ [(Assert, (BArray256.is_init b_P 0 256))]);
    b__x <- (BArray256.init_arr (W8.of_int 0));
    b__y <- (BArray256.init_arr (W8.of_int 0));
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 256) <= 1032)))]);
    b_t <- (SBArray1032_256.get_sub64 b_ctx 0);
    t <- (SBArray1032_256.get_sub64 ctx 0);
    b_param <- b_t;
    param <- t;
    param_0 <- p;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    t <- result;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 256) <= 1032)))]);
    b_ctx <-
    (SBArray1032_256.set_sub64 b_ctx 0 (BArray256.init_arr (W8.of_int 255)));
    ctx <- (SBArray1032_256.set_sub64 ctx 0 t);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 256) <= 1032)))]);
    b_t <- (SBArray1032_256.get_sub64 b_ctx 32);
    t <- (SBArray1032_256.get_sub64 ctx 32);
    b_param_0 <- b_t;
    param_1 <- t;
    param_2 <- p;
    (aux_1, aux_2, aux_3, tmp__trace) <@ h__BN___neg_ (param_1, b_param_0,
    param_2, (BArray256.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray256.is_init b_result_0 0 256))]);
    t <- result_1;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 256) <= 1032)))]);
    b_ctx <-
    (SBArray1032_256.set_sub64 b_ctx 32 (BArray256.init_arr (W8.of_int 255)));
    ctx <- (SBArray1032_256.set_sub64 ctx 32 t);
    p0 <- (BArray256.get64 p 0);
    inv <- p0;
    j <- 0;
    while ((j < 5)) {
      d <- p0;
      d <- (d * inv);
      d <- (- d);
      d <- (d + (W64.of_int 2));
      inv <- (inv * d);
      j <- (j + 1);
    }
    u0 <- (- inv);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (128 * 8)) /\ (((128 * 8) + 8) <= 1032)))]);
    b_ctx <-
    (BArray1032.set64d b_ctx (128 * 8) (W64.of_int 18446744073709551615));
    ctx <- (BArray1032.set64 ctx 128 u0);
    b_x <- b__x;
    x <- _x;
    b_param_1 <- b_x;
    param_3 <- x;
    (aux_4, aux_5, tmp__trace) <@ h__BN___set0_ (param_3, b_param_1);
    result_2 <- aux_4;
    b_result_1 <- aux_5;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray256.is_init b_result_1 0 256))]);
    x <- result_2;
    x <- (BArray256.set64 x 0 (W64.of_int 1));
    _x <- x;
    i <- (W64.of_int (32 * 32));
    while (((W64.of_int 0) \ult i)) {
      _i <- i;
      x <- _x;
      b_y <- b__y;
      y <- _y;
      b_param_2 <- b_y;
      param_4 <- y;
      param_5 <- x;
      param_6 <- x;
      b_param_3 <- b_ctx;
      param_7 <- ctx;
      (aux_6, aux_7, tmp__trace) <@ h__FPM___addm_ (param_4, b_param_2,
      param_5, (BArray256.init_arr (W8.of_int 255)), param_6,
      (BArray256.init_arr (W8.of_int 255)), param_7, b_param_3);
      result_3 <- aux_6;
      b_result_2 <- aux_7;
      trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
      trace_h__FPM___ctx_init_ <-
      (trace_h__FPM___ctx_init_ ++
      [(Assert, (BArray256.is_init b_result_2 0 256))]);
      y <- result_3;
      b__y <- (BArray256.init_arr (W8.of_int 255));
      _y <- y;
      x <- _x;
      y <- _y;
      param_8 <- x;
      param_9 <- y;
      param_10 <- y;
      b_param_4 <- b_ctx;
      param_11 <- ctx;
      (aux_8, aux_9, tmp__trace) <@ h__FPM___addm_ (param_8,
      (BArray256.init_arr (W8.of_int 255)), param_9,
      (BArray256.init_arr (W8.of_int 255)), param_10,
      (BArray256.init_arr (W8.of_int 255)), param_11, b_param_4);
      result_4 <- aux_8;
      b_result_3 <- aux_9;
      trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
      trace_h__FPM___ctx_init_ <-
      (trace_h__FPM___ctx_init_ ++
      [(Assert, (BArray256.is_init b_result_3 0 256))]);
      x <- result_4;
      _x <- x;
      i <- _i;
      i <- (i - (W64.of_int 1));
    }
    x <- _x;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (64 * 8)) /\ (((64 * 8) + 256) <= 1032)))]);
    b_t <- (SBArray1032_256.get_sub64 b_ctx 64);
    t <- (SBArray1032_256.get_sub64 ctx 64);
    b_param_5 <- b_t;
    param_12 <- t;
    param_13 <- x;
    (aux_10, aux_11, tmp__trace) <@ h__BN___mov_ (param_12, b_param_5,
    param_13, (BArray256.init_arr (W8.of_int 255)));
    result_5 <- aux_10;
    b_result_4 <- aux_11;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray256.is_init b_result_4 0 256))]);
    t <- result_5;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (64 * 8)) /\ (((64 * 8) + 256) <= 1032)))]);
    b_ctx <-
    (SBArray1032_256.set_sub64 b_ctx 64 (BArray256.init_arr (W8.of_int 255)));
    ctx <- (SBArray1032_256.set_sub64 ctx 64 t);
    i <- (W64.of_int (32 * 32));
    while (((W64.of_int 0) \ult i)) {
      _i <- i;
      x <- _x;
      b_y <- b__y;
      y <- _y;
      b_param_6 <- b_y;
      param_14 <- y;
      param_15 <- x;
      param_16 <- x;
      b_param_7 <- b_ctx;
      param_17 <- ctx;
      (aux_12, aux_13, tmp__trace) <@ h__FPM___addm_ (param_14, b_param_6,
      param_15, (BArray256.init_arr (W8.of_int 255)), param_16,
      (BArray256.init_arr (W8.of_int 255)), param_17, b_param_7);
      result_6 <- aux_12;
      b_result_5 <- aux_13;
      trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
      trace_h__FPM___ctx_init_ <-
      (trace_h__FPM___ctx_init_ ++
      [(Assert, (BArray256.is_init b_result_5 0 256))]);
      y <- result_6;
      b__y <- (BArray256.init_arr (W8.of_int 255));
      _y <- y;
      x <- _x;
      y <- _y;
      param_18 <- x;
      param_19 <- y;
      param_20 <- y;
      b_param_8 <- b_ctx;
      param_21 <- ctx;
      (aux_14, aux_15, tmp__trace) <@ h__FPM___addm_ (param_18,
      (BArray256.init_arr (W8.of_int 255)), param_19,
      (BArray256.init_arr (W8.of_int 255)), param_20,
      (BArray256.init_arr (W8.of_int 255)), param_21, b_param_8);
      result_7 <- aux_14;
      b_result_6 <- aux_15;
      trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
      trace_h__FPM___ctx_init_ <-
      (trace_h__FPM___ctx_init_ ++
      [(Assert, (BArray256.is_init b_result_6 0 256))]);
      x <- result_7;
      _x <- x;
      i <- _i;
      i <- (i - (W64.of_int 1));
    }
    x <- _x;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (96 * 8)) /\ (((96 * 8) + 256) <= 1032)))]);
    b_t <- (SBArray1032_256.get_sub64 b_ctx 96);
    t <- (SBArray1032_256.get_sub64 ctx 96);
    b_param_9 <- b_t;
    param_22 <- t;
    param_23 <- x;
    (aux_16, aux_17, tmp__trace) <@ h__BN___mov_ (param_22, b_param_9,
    param_23, (BArray256.init_arr (W8.of_int 255)));
    result_8 <- aux_16;
    b_result_7 <- aux_17;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray256.is_init b_result_7 0 256))]);
    t <- result_8;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (96 * 8)) /\ (((96 * 8) + 256) <= 1032)))]);
    b_ctx <-
    (SBArray1032_256.set_sub64 b_ctx 96 (BArray256.init_arr (W8.of_int 255)));
    ctx <- (SBArray1032_256.set_sub64 ctx 96 t);
    return (ctx, b_ctx, trace_h__FPM___ctx_init_);
  }
  proc h__FPM__EXPE___exp1mLR_first_noct (r:BArray256.t, b_r:BArray256.t,
                                          x:BArray256.t, b_x:BArray256.t,
                                          w:W64.t, ctx:BArray1032.t,
                                          b_ctx:BArray1032.t) : BArray256.t *
                                                                BArray256.t *
                                                                trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var aux_3:BArray256.t;
    var aux_4:BArray256.t;
    var _x:BArray256.t;
    var _ctx:BArray1032.t;
    var k:W64.t;
    var cf:bool;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var _k:W64.t;
    var _w:W64.t;
    var param_1:BArray256.t;
    var param_2:BArray1032.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var param_3:BArray256.t;
    var param_4:BArray256.t;
    var param_5:BArray1032.t;
    var result_1:BArray256.t;
    var b_result_1:BArray256.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var trace_h__FPM__EXPE___exp1mLR_first_noct:trace;
    _ctx <- witness;
    _x <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_h__FPM__EXPE___exp1mLR_first_noct <- [];
    trace_h__FPM__EXPE___exp1mLR_first_noct <-
    (trace_h__FPM__EXPE___exp1mLR_first_noct ++
    [(Assert,
     ((BArray256.is_init b_x 0 256) /\ (BArray1032.is_init b_ctx 0 1032)))]);
    _x <- x;
    _ctx <- ctx;
    k <- (W64.of_int 64);
    ( _0, cf,  _1,  _2,  _3, w) <- (SHL_64 w (W8.of_int 1));
    while ((! cf)) {
      k <- (k - (W64.of_int 1));
      ( _4, cf,  _5,  _6,  _7, w) <- (SHL_64 w (W8.of_int 1));
    }
    b_param <- b_r;
    param <- r;
    param_0 <- x;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__EXPE___exp1mLR_first_noct <-
    (trace_h__FPM__EXPE___exp1mLR_first_noct ++ tmp__trace);
    trace_h__FPM__EXPE___exp1mLR_first_noct <-
    (trace_h__FPM__EXPE___exp1mLR_first_noct ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    k <- (k - (W64.of_int 1));
    while (((W64.of_int 0) \slt k)) {
      _k <- k;
      _w <- w;
      ctx <- _ctx;
      param_1 <- r;
      param_2 <- ctx;
      (aux_1, aux_2, tmp__trace) <@ h__FPM__fun_sqrU (param_1,
      (BArray256.init_arr (W8.of_int 255)), param_2,
      (BArray1032.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__FPM__EXPE___exp1mLR_first_noct <-
      (trace_h__FPM__EXPE___exp1mLR_first_noct ++ tmp__trace);
      trace_h__FPM__EXPE___exp1mLR_first_noct <-
      (trace_h__FPM__EXPE___exp1mLR_first_noct ++
      [(Assert, (BArray256.is_init b_result_0 0 256))]);
      r <- result_0;
      w <- _w;
      ( _8, cf,  _9,  _10,  _11, w) <- (SHL_64 w (W8.of_int 1));
      _w <- w;
      if (cf) {
        x <- _x;
        ctx <- _ctx;
        param_3 <- r;
        param_4 <- x;
        param_5 <- ctx;
        (aux_3, aux_4, tmp__trace) <@ h__FPM__fun_mulU (param_3,
        (BArray256.init_arr (W8.of_int 255)), param_4,
        (BArray256.init_arr (W8.of_int 255)), param_5,
        (BArray1032.init_arr (W8.of_int 255)));
        result_1 <- aux_3;
        b_result_1 <- aux_4;
        trace_h__FPM__EXPE___exp1mLR_first_noct <-
        (trace_h__FPM__EXPE___exp1mLR_first_noct ++ tmp__trace);
        trace_h__FPM__EXPE___exp1mLR_first_noct <-
        (trace_h__FPM__EXPE___exp1mLR_first_noct ++
        [(Assert, (BArray256.is_init b_result_1 0 256))]);
        r <- result_1;
      } else {
        
      }
      w <- _w;
      k <- _k;
      k <- (k - (W64.of_int 1));
    }
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__EXPE___exp1mLR_first_noct);
  }
  proc h__FPM__EXPE___exp1mLR_noct (r:BArray256.t, b_r:BArray256.t,
                                    x:BArray256.t, b_x:BArray256.t, w:W64.t,
                                    ctx:BArray1032.t, b_ctx:BArray1032.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var _x:BArray256.t;
    var _ctx:BArray1032.t;
    var k:W64.t;
    var _k:W64.t;
    var _w:W64.t;
    var param:BArray256.t;
    var param_0:BArray1032.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var cf:bool;
    var param_1:BArray256.t;
    var param_2:BArray256.t;
    var param_3:BArray1032.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__FPM__EXPE___exp1mLR_noct:trace;
    _ctx <- witness;
    _x <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__FPM__EXPE___exp1mLR_noct <- [];
    trace_h__FPM__EXPE___exp1mLR_noct <-
    (trace_h__FPM__EXPE___exp1mLR_noct ++
    [(Assert, (BArray256.is_init b_r 0 256))]);
    trace_h__FPM__EXPE___exp1mLR_noct <-
    (trace_h__FPM__EXPE___exp1mLR_noct ++
    [(Assert, (BArray256.is_init b_x 0 256))]);
    trace_h__FPM__EXPE___exp1mLR_noct <-
    (trace_h__FPM__EXPE___exp1mLR_noct ++
    [(Assert, (BArray1032.is_init b_ctx 0 1032))]);
    _x <- x;
    _ctx <- ctx;
    k <- (W64.of_int 64);
    while (((W64.of_int 0) \slt k)) {
      _k <- k;
      _w <- w;
      ctx <- _ctx;
      param <- r;
      param_0 <- ctx;
      (aux, aux_0, tmp__trace) <@ h__FPM__fun_sqrU (param,
      (BArray256.init_arr (W8.of_int 255)), param_0,
      (BArray1032.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__FPM__EXPE___exp1mLR_noct <-
      (trace_h__FPM__EXPE___exp1mLR_noct ++ tmp__trace);
      trace_h__FPM__EXPE___exp1mLR_noct <-
      (trace_h__FPM__EXPE___exp1mLR_noct ++
      [(Assert, (BArray256.is_init b_result 0 256))]);
      r <- result;
      w <- _w;
      ( _0, cf,  _1,  _2,  _3, w) <- (SHL_64 w (W8.of_int 1));
      _w <- w;
      if (cf) {
        x <- _x;
        ctx <- _ctx;
        param_1 <- r;
        param_2 <- x;
        param_3 <- ctx;
        (aux_1, aux_2, tmp__trace) <@ h__FPM__fun_mulU (param_1,
        (BArray256.init_arr (W8.of_int 255)), param_2,
        (BArray256.init_arr (W8.of_int 255)), param_3,
        (BArray1032.init_arr (W8.of_int 255)));
        result_0 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__FPM__EXPE___exp1mLR_noct <-
        (trace_h__FPM__EXPE___exp1mLR_noct ++ tmp__trace);
        trace_h__FPM__EXPE___exp1mLR_noct <-
        (trace_h__FPM__EXPE___exp1mLR_noct ++
        [(Assert, (BArray256.is_init b_result_0 0 256))]);
        r <- result_0;
      } else {
        
      }
      w <- _w;
      k <- _k;
      k <- (k - (W64.of_int 1));
    }
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__EXPE___exp1mLR_noct);
  }
  proc h__FPM__EXPE___expmLR_noct (r:BArray256.t, b_r:BArray256.t,
                                   x:BArray256.t, b_x:BArray256.t,
                                   e:BArray32.t, b_e:BArray32.t,
                                   ctx:BArray1032.t, b_ctx:BArray1032.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var aux_3:BArray256.t;
    var aux_4:BArray256.t;
    var _x:BArray256.t;
    var _e:BArray32.t;
    var _ctx:BArray1032.t;
    var i:W64.t;
    var w:W64.t;
    var i_s:W64.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:W64.t;
    var param_2:BArray1032.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var b_exp0:BArray256.t;
    var exp0:BArray256.t;
    var b_param_0:BArray256.t;
    var param_3:BArray256.t;
    var b_param_1:BArray256.t;
    var param_4:BArray256.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var param_5:BArray256.t;
    var param_6:BArray256.t;
    var param_7:W64.t;
    var param_8:BArray1032.t;
    var result_1:BArray256.t;
    var b_result_1:BArray256.t;
    var trace_h__FPM__EXPE___expmLR_noct:trace;
    _ctx <- witness;
    _e <- witness;
    _x <- witness;
    b_exp0 <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    exp0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_8 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_h__FPM__EXPE___expmLR_noct <- [];
    trace_h__FPM__EXPE___expmLR_noct <-
    (trace_h__FPM__EXPE___expmLR_noct ++
    [(Assert,
     (((BArray256.is_init b_x 0 256) /\ (BArray32.is_init b_e 0 32)) /\
     (BArray1032.is_init b_ctx 0 1032)))]);
    _x <- x;
    _e <- e;
    _ctx <- ctx;
    i <- (W64.of_int (4 - 1));
    trace_h__FPM__EXPE___expmLR_noct <-
    (trace_h__FPM__EXPE___expmLR_noct ++
    [(Assert,
     ((0 <= ((W64.to_uint i) * 8)) /\ ((((W64.to_uint i) * 8) + 8) <= 32)))]);
    w <- (BArray32.get64 e (W64.to_uint i));
    while ((w = (W64.of_int 0))) {
      i <- (i - (W64.of_int 1));
      if (((W64.of_int 0) \sle i)) {
        trace_h__FPM__EXPE___expmLR_noct <-
        (trace_h__FPM__EXPE___expmLR_noct ++
        [(Assert,
         ((0 <= ((W64.to_uint i) * 8)) /\
         ((((W64.to_uint i) * 8) + 8) <= 32)))]);
        w <- (BArray32.get64 e (W64.to_uint i));
      } else {
        w <- (W64.of_int 1);
      }
    }
    if (((W64.of_int 0) \sle i)) {
      i_s <- i;
      x <- _x;
      ctx <- _ctx;
      b_param <- b_r;
      param <- r;
      param_0 <- x;
      param_1 <- w;
      param_2 <- ctx;
      (aux_1, aux_2, tmp__trace) <@ h__FPM__EXPE___exp1mLR_first_noct (
      param, b_param, param_0, (BArray256.init_arr (W8.of_int 255)), 
      param_1, param_2, (BArray1032.init_arr (W8.of_int 255)));
      result <- aux_1;
      b_result <- aux_2;
      trace_h__FPM__EXPE___expmLR_noct <-
      (trace_h__FPM__EXPE___expmLR_noct ++ tmp__trace);
      trace_h__FPM__EXPE___expmLR_noct <-
      (trace_h__FPM__EXPE___expmLR_noct ++
      [(Assert, (BArray256.is_init b_result 0 256))]);
      r <- result;
      i <- i_s;
      i <- (i - (W64.of_int 1));
    } else {
      trace_h__FPM__EXPE___expmLR_noct <-
      (trace_h__FPM__EXPE___expmLR_noct ++
      [(Assert, ((0 <= (64 * 8)) /\ (((64 * 8) + 256) <= 1032)))]);
      b_exp0 <- (SBArray1032_256.get_sub64 b_ctx 64);
      exp0 <- (SBArray1032_256.get_sub64 ctx 64);
      b_param_0 <- b_r;
      param_3 <- r;
      b_param_1 <- b_exp0;
      param_4 <- exp0;
      (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param_3, b_param_0, param_4,
      b_param_1);
      result_0 <- aux;
      b_result_0 <- aux_0;
      trace_h__FPM__EXPE___expmLR_noct <-
      (trace_h__FPM__EXPE___expmLR_noct ++ tmp__trace);
      trace_h__FPM__EXPE___expmLR_noct <-
      (trace_h__FPM__EXPE___expmLR_noct ++
      [(Assert, (BArray256.is_init b_result_0 0 256))]);
      r <- result_0;
    }
    while (((W64.of_int 0) \sle i)) {
      e <- _e;
      trace_h__FPM__EXPE___expmLR_noct <-
      (trace_h__FPM__EXPE___expmLR_noct ++
      [(Assert,
       ((0 <= ((W64.to_uint i) * 8)) /\ ((((W64.to_uint i) * 8) + 8) <= 32)))]);
      w <- (BArray32.get64 e (W64.to_uint i));
      i_s <- i;
      x <- _x;
      ctx <- _ctx;
      param_5 <- r;
      param_6 <- x;
      param_7 <- w;
      param_8 <- ctx;
      (aux_3, aux_4, tmp__trace) <@ h__FPM__EXPE___exp1mLR_noct (param_5,
      (BArray256.init_arr (W8.of_int 255)), param_6,
      (BArray256.init_arr (W8.of_int 255)), param_7, param_8,
      (BArray1032.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__FPM__EXPE___expmLR_noct <-
      (trace_h__FPM__EXPE___expmLR_noct ++ tmp__trace);
      trace_h__FPM__EXPE___expmLR_noct <-
      (trace_h__FPM__EXPE___expmLR_noct ++
      [(Assert, (BArray256.is_init b_result_1 0 256))]);
      r <- result_1;
      i <- i_s;
      i <- (i - (W64.of_int 1));
    }
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__EXPE___expmLR_noct);
  }
  proc h__FPM__EXPE___expmLR_noct_ (r:BArray256.t, b_r:BArray256.t,
                                    a:BArray256.t, b_a:BArray256.t,
                                    b:BArray32.t, b_b:BArray32.t,
                                    ctx:BArray1032.t, b_ctx:BArray1032.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var b_exp0:BArray256.t;
    var exp0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var b_param_0:BArray256.t;
    var param_0:BArray256.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var param_1:BArray256.t;
    var param_2:BArray256.t;
    var param_3:BArray32.t;
    var param_4:BArray1032.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var trace_h__FPM__EXPE___expmLR_noct_:trace;
    b_exp0 <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    exp0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__FPM__EXPE___expmLR_noct_ <- [];
    trace_h__FPM__EXPE___expmLR_noct_ <-
    (trace_h__FPM__EXPE___expmLR_noct_ ++
    [(Assert,
     (((BArray256.is_init b_a 0 256) /\ (BArray32.is_init b_b 0 32)) /\
     (BArray1032.is_init b_ctx 0 1032)))]);
    trace_h__FPM__EXPE___expmLR_noct_ <-
    (trace_h__FPM__EXPE___expmLR_noct_ ++
    [(Assert, ((0 <= (64 * 8)) /\ (((64 * 8) + 256) <= 1032)))]);
    b_exp0 <- (SBArray1032_256.get_sub64 b_ctx 64);
    exp0 <- (SBArray1032_256.get_sub64 ctx 64);
    b_param <- b_r;
    param <- r;
    b_param_0 <- b_exp0;
    param_0 <- exp0;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    b_param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__EXPE___expmLR_noct_ <-
    (trace_h__FPM__EXPE___expmLR_noct_ ++ tmp__trace);
    trace_h__FPM__EXPE___expmLR_noct_ <-
    (trace_h__FPM__EXPE___expmLR_noct_ ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    r <- result;
    a <- a;
    b <- b;
    param_1 <- r;
    param_2 <- a;
    param_3 <- b;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM__EXPE___expmLR_noct (param_1,
    (BArray256.init_arr (W8.of_int 255)), param_2,
    (BArray256.init_arr (W8.of_int 255)), param_3,
    (BArray32.init_arr (W8.of_int 255)), param_4,
    (BArray1032.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM__EXPE___expmLR_noct_ <-
    (trace_h__FPM__EXPE___expmLR_noct_ ++ tmp__trace);
    trace_h__FPM__EXPE___expmLR_noct_ <-
    (trace_h__FPM__EXPE___expmLR_noct_ ++
    [(Assert, (BArray256.is_init b_result_0 0 256))]);
    r <- result_0;
    r <- r;
    b_r <- (BArray256.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__EXPE___expmLR_noct_);
  }
  proc h__RSA___ctx_init_N (ctx:BArray1032.t, b_ctx:BArray1032.t,
                            n:BArray256.t, b_n:BArray256.t) : BArray1032.t *
                                                              BArray1032.t *
                                                              trace = {
    var aux:BArray1032.t;
    var aux_0:BArray1032.t;
    var b_param:BArray1032.t;
    var param:BArray1032.t;
    var param_0:BArray256.t;
    var result:BArray1032.t;
    var b_result:BArray1032.t;
    var trace_h__RSA___ctx_init_N:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__RSA___ctx_init_N <- [];
    trace_h__RSA___ctx_init_N <-
    (trace_h__RSA___ctx_init_N ++ [(Assert, (BArray256.is_init b_n 0 256))]);
    b_param <- b_ctx;
    param <- ctx;
    param_0 <- n;
    (aux, aux_0, tmp__trace) <@ h__FPM___ctx_init_ (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__RSA___ctx_init_N <- (trace_h__RSA___ctx_init_N ++ tmp__trace);
    trace_h__RSA___ctx_init_N <-
    (trace_h__RSA___ctx_init_N ++
    [(Assert, (BArray1032.is_init b_result 0 1032))]);
    ctx <- result;
    b_ctx <- (BArray1032.init_arr (W8.of_int 255));
    return (ctx, b_ctx, trace_h__RSA___ctx_init_N);
  }
  proc h__RSA___ctx_init_P (ctx:BArray520.t, b_ctx:BArray520.t,
                            p:BArray128.t, b_p:BArray128.t) : BArray520.t *
                                                              BArray520.t *
                                                              trace = {
    var aux:BArray520.t;
    var aux_0:BArray520.t;
    var b_param:BArray520.t;
    var param:BArray520.t;
    var param_0:BArray128.t;
    var result:BArray520.t;
    var b_result:BArray520.t;
    var trace_h__RSA___ctx_init_P:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__RSA___ctx_init_P <- [];
    trace_h__RSA___ctx_init_P <-
    (trace_h__RSA___ctx_init_P ++ [(Assert, (BArray128.is_init b_p 0 128))]);
    b_param <- b_ctx;
    param <- ctx;
    param_0 <- p;
    (aux, aux_0, tmp__trace) <@ h__H__FPM___ctx_init_ (param, b_param,
    param_0, (BArray128.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__RSA___ctx_init_P <- (trace_h__RSA___ctx_init_P ++ tmp__trace);
    trace_h__RSA___ctx_init_P <-
    (trace_h__RSA___ctx_init_P ++
    [(Assert, (BArray520.is_init b_result 0 520))]);
    ctx <- result;
    b_ctx <- (BArray520.init_arr (W8.of_int 255));
    return (ctx, b_ctx, trace_h__RSA___ctx_init_P);
  }
  proc h__RSA____RSA_expand_pk (pK:BArray1064.t, b_PK:BArray1064.t,
                                pk:BArray288.t, b_pk:BArray288.t) : BArray1064.t *
                                                                    BArray1064.t *
                                                                    trace = {
    var aux:BArray1032.t;
    var aux_0:BArray1032.t;
    var _pk:BArray288.t;
    var b_ctx:BArray1032.t;
    var ctx:BArray1032.t;
    var b_n:BArray256.t;
    var n:BArray256.t;
    var b_param:BArray1032.t;
    var param:BArray1032.t;
    var b_param_0:BArray256.t;
    var param_0:BArray256.t;
    var result:BArray1032.t;
    var b_result:BArray1032.t;
    var i:int;
    var t:W64.t;
    var trace_h__RSA____RSA_expand_pk:trace;
    _pk <- witness;
    b_ctx <- witness;
    b_n <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    ctx <- witness;
    n <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__RSA____RSA_expand_pk <- [];
    trace_h__RSA____RSA_expand_pk <-
    (trace_h__RSA____RSA_expand_pk ++
    [(Assert, (BArray288.is_init b_pk 0 288))]);
    _pk <- pk;
    trace_h__RSA____RSA_expand_pk <-
    (trace_h__RSA____RSA_expand_pk ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 1032) <= 1064)))]);
    b_ctx <- (SBArray1064_1032.get_sub64 b_PK 0);
    ctx <- (SBArray1064_1032.get_sub64 pK 0);
    trace_h__RSA____RSA_expand_pk <-
    (trace_h__RSA____RSA_expand_pk ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 256) <= 288)))]);
    b_n <- (SBArray288_256.get_sub64 b_pk 0);
    n <- (SBArray288_256.get_sub64 pk 0);
    b_param <- b_ctx;
    param <- ctx;
    b_param_0 <- b_n;
    param_0 <- n;
    (aux, aux_0, tmp__trace) <@ h__RSA___ctx_init_N (param, b_param, 
    param_0, b_param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__RSA____RSA_expand_pk <-
    (trace_h__RSA____RSA_expand_pk ++ tmp__trace);
    trace_h__RSA____RSA_expand_pk <-
    (trace_h__RSA____RSA_expand_pk ++
    [(Assert, (BArray1032.is_init b_result 0 1032))]);
    ctx <- result;
    trace_h__RSA____RSA_expand_pk <-
    (trace_h__RSA____RSA_expand_pk ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 1032) <= 1064)))]);
    b_PK <-
    (SBArray1064_1032.set_sub64 b_PK 0 (BArray1032.init_arr (W8.of_int 255)));
    pK <- (SBArray1064_1032.set_sub64 pK 0 ctx);
    pk <- _pk;
    i <- 0;
    while ((i < 4)) {
      trace_h__RSA____RSA_expand_pk <-
      (trace_h__RSA____RSA_expand_pk ++
      [(Assert, ((0 <= ((32 + i) * 8)) /\ ((((32 + i) * 8) + 8) <= 288)))]);
      t <- (BArray288.get64 pk (32 + i));
      trace_h__RSA____RSA_expand_pk <-
      (trace_h__RSA____RSA_expand_pk ++
      [(Assert, ((0 <= ((129 + i) * 8)) /\ ((((129 + i) * 8) + 8) <= 1064)))]);
      b_PK <-
      (BArray1064.set64d b_PK ((129 + i) * 8)
      (W64.of_int 18446744073709551615));
      pK <- (BArray1064.set64 pK (129 + i) t);
      i <- (i + 1);
    }
    return (pK, b_PK, trace_h__RSA____RSA_expand_pk);
  }
  proc h__RSA____RSA_expand_sk (sK:BArray1424.t, b_SK:BArray1424.t,
                                sk:BArray640.t, b_sk:BArray640.t) : BArray1424.t *
                                                                    BArray1424.t *
                                                                    trace = {
    var aux_3:BArray128.t;
    var aux_4:BArray128.t;
    var aux_5:BArray128.t;
    var aux_6:BArray128.t;
    var aux_7:BArray128.t;
    var aux_8:BArray128.t;
    var aux:BArray520.t;
    var aux_0:BArray520.t;
    var aux_1:BArray520.t;
    var aux_2:BArray520.t;
    var _sk:BArray640.t;
    var b_ctx:BArray520.t;
    var ctx:BArray520.t;
    var b_x:BArray128.t;
    var x:BArray128.t;
    var b_param:BArray520.t;
    var param:BArray520.t;
    var b_param_0:BArray128.t;
    var param_0:BArray128.t;
    var result:BArray520.t;
    var b_result:BArray520.t;
    var b_param_1:BArray520.t;
    var param_1:BArray520.t;
    var b_param_2:BArray128.t;
    var param_2:BArray128.t;
    var result_0:BArray520.t;
    var b_result_0:BArray520.t;
    var b_y:BArray128.t;
    var y:BArray128.t;
    var b_param_3:BArray128.t;
    var param_3:BArray128.t;
    var b_param_4:BArray128.t;
    var param_4:BArray128.t;
    var result_1:BArray128.t;
    var b_result_1:BArray128.t;
    var b_param_5:BArray128.t;
    var param_5:BArray128.t;
    var b_param_6:BArray128.t;
    var param_6:BArray128.t;
    var result_2:BArray128.t;
    var b_result_2:BArray128.t;
    var b_param_7:BArray128.t;
    var param_7:BArray128.t;
    var b_param_8:BArray128.t;
    var param_8:BArray128.t;
    var result_3:BArray128.t;
    var b_result_3:BArray128.t;
    var trace_h__RSA____RSA_expand_sk:trace;
    _sk <- witness;
    b_ctx <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    b_param_7 <- witness;
    b_param_8 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_x <- witness;
    b_y <- witness;
    ctx <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    x <- witness;
    y <- witness;
    trace_h__RSA____RSA_expand_sk <- [];
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, (BArray640.is_init b_sk 0 640))]);
    _sk <- sk;
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 520) <= 1424)))]);
    b_ctx <- (SBArray1424_520.get_sub64 b_SK 0);
    ctx <- (SBArray1424_520.get_sub64 sK 0);
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 128) <= 640)))]);
    b_x <- (SBArray640_128.get_sub64 b_sk 0);
    x <- (SBArray640_128.get_sub64 sk 0);
    b_param <- b_ctx;
    param <- ctx;
    b_param_0 <- b_x;
    param_0 <- x;
    (aux, aux_0, tmp__trace) <@ h__RSA___ctx_init_P (param, b_param, 
    param_0, b_param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++ tmp__trace);
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, (BArray520.is_init b_result 0 520))]);
    ctx <- result;
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 520) <= 1424)))]);
    b_SK <-
    (SBArray1424_520.set_sub64 b_SK 0 (BArray520.init_arr (W8.of_int 255)));
    sK <- (SBArray1424_520.set_sub64 sK 0 ctx);
    b_sk <- (BArray640.init_arr (W8.of_int 255));
    sk <- _sk;
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (65 * 8)) /\ (((65 * 8) + 520) <= 1424)))]);
    b_ctx <- (SBArray1424_520.get_sub64 b_SK 65);
    ctx <- (SBArray1424_520.get_sub64 sK 65);
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 640)))]);
    b_x <- (SBArray640_128.get_sub64 b_sk 16);
    x <- (SBArray640_128.get_sub64 sk 16);
    b_param_1 <- b_ctx;
    param_1 <- ctx;
    b_param_2 <- b_x;
    param_2 <- x;
    (aux_1, aux_2, tmp__trace) <@ h__RSA___ctx_init_P (param_1, b_param_1,
    param_2, b_param_2);
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++ tmp__trace);
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, (BArray520.is_init b_result_0 0 520))]);
    ctx <- result_0;
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (65 * 8)) /\ (((65 * 8) + 520) <= 1424)))]);
    b_SK <-
    (SBArray1424_520.set_sub64 b_SK 65 (BArray520.init_arr (W8.of_int 255)));
    sK <- (SBArray1424_520.set_sub64 sK 65 ctx);
    b_sk <- (BArray640.init_arr (W8.of_int 255));
    sk <- _sk;
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (130 * 8)) /\ (((130 * 8) + 128) <= 1424)))]);
    b_x <- (SBArray1424_128.get_sub64 b_SK 130);
    x <- (SBArray1424_128.get_sub64 sK 130);
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (32 * 8)) /\ (((32 * 8) + 128) <= 640)))]);
    b_y <- (SBArray640_128.get_sub64 b_sk 32);
    y <- (SBArray640_128.get_sub64 sk 32);
    b_param_3 <- b_x;
    param_3 <- x;
    b_param_4 <- b_y;
    param_4 <- y;
    (aux_3, aux_4, tmp__trace) <@ h__H__BN___mov_ (param_3, b_param_3,
    param_4, b_param_4);
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++ tmp__trace);
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, (BArray128.is_init b_result_1 0 128))]);
    x <- result_1;
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (130 * 8)) /\ (((130 * 8) + 128) <= 1424)))]);
    b_SK <-
    (SBArray1424_128.set_sub64 b_SK 130 (BArray128.init_arr (W8.of_int 255)));
    sK <- (SBArray1424_128.set_sub64 sK 130 x);
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (146 * 8)) /\ (((146 * 8) + 128) <= 1424)))]);
    b_x <- (SBArray1424_128.get_sub64 b_SK 146);
    x <- (SBArray1424_128.get_sub64 sK 146);
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (48 * 8)) /\ (((48 * 8) + 128) <= 640)))]);
    b_y <- (SBArray640_128.get_sub64 b_sk 48);
    y <- (SBArray640_128.get_sub64 sk 48);
    b_param_5 <- b_x;
    param_5 <- x;
    b_param_6 <- b_y;
    param_6 <- y;
    (aux_5, aux_6, tmp__trace) <@ h__H__BN___mov_ (param_5, b_param_5,
    param_6, b_param_6);
    result_2 <- aux_5;
    b_result_2 <- aux_6;
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++ tmp__trace);
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, (BArray128.is_init b_result_2 0 128))]);
    x <- result_2;
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (146 * 8)) /\ (((146 * 8) + 128) <= 1424)))]);
    b_SK <-
    (SBArray1424_128.set_sub64 b_SK 146 (BArray128.init_arr (W8.of_int 255)));
    sK <- (SBArray1424_128.set_sub64 sK 146 x);
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (162 * 8)) /\ (((162 * 8) + 128) <= 1424)))]);
    b_x <- (SBArray1424_128.get_sub64 b_SK 162);
    x <- (SBArray1424_128.get_sub64 sK 162);
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (64 * 8)) /\ (((64 * 8) + 128) <= 640)))]);
    b_y <- (SBArray640_128.get_sub64 b_sk 64);
    y <- (SBArray640_128.get_sub64 sk 64);
    b_param_7 <- b_x;
    param_7 <- x;
    b_param_8 <- b_y;
    param_8 <- y;
    (aux_7, aux_8, tmp__trace) <@ h__H__BN___mov_ (param_7, b_param_7,
    param_8, b_param_8);
    result_3 <- aux_7;
    b_result_3 <- aux_8;
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++ tmp__trace);
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, (BArray128.is_init b_result_3 0 128))]);
    x <- result_3;
    trace_h__RSA____RSA_expand_sk <-
    (trace_h__RSA____RSA_expand_sk ++
    [(Assert, ((0 <= (162 * 8)) /\ (((162 * 8) + 128) <= 1424)))]);
    b_SK <-
    (SBArray1424_128.set_sub64 b_SK 162 (BArray128.init_arr (W8.of_int 255)));
    sK <- (SBArray1424_128.set_sub64 sK 162 x);
    return (sK, b_SK, trace_h__RSA____RSA_expand_sk);
  }
  proc h__RSA____RSAVP1 (y:BArray256.t, b_y:BArray256.t, s:BArray256.t,
                         b_s:BArray256.t, pk:BArray1064.t, b_pk:BArray1064.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var aux_3:BArray256.t;
    var aux_4:BArray256.t;
    var aux_5:BArray256.t;
    var aux_6:BArray256.t;
    var b_x:BArray256.t;
    var _pk:BArray1064.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var x:BArray256.t;
    var param_0:BArray256.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var b_ctx_n:BArray1032.t;
    var ctx_n:BArray1032.t;
    var param_1:BArray256.t;
    var b_param_0:BArray1032.t;
    var param_2:BArray1032.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var b_e:BArray32.t;
    var e:BArray32.t;
    var b_param_1:BArray256.t;
    var param_3:BArray256.t;
    var param_4:BArray256.t;
    var b_param_2:BArray32.t;
    var param_5:BArray32.t;
    var b_param_3:BArray1032.t;
    var param_6:BArray1032.t;
    var result_1:BArray256.t;
    var b_result_1:BArray256.t;
    var param_7:BArray256.t;
    var b_param_4:BArray1032.t;
    var param_8:BArray1032.t;
    var result_2:BArray256.t;
    var b_result_2:BArray256.t;
    var trace_h__RSA____RSAVP1:trace;
    _pk <- witness;
    b_ctx_n <- witness;
    b_e <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_x <- witness;
    ctx_n <- witness;
    e <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    x <- witness;
    trace_h__RSA____RSAVP1 <- [];
    trace_h__RSA____RSAVP1 <-
    (trace_h__RSA____RSAVP1 ++
    [(Assert,
     ((BArray256.is_init b_s 0 256) /\ (BArray1064.is_init b_pk 0 1064)))]);
    b_x <- (BArray256.init_arr (W8.of_int 0));
    _pk <- pk;
    b_param <- b_x;
    param <- x;
    param_0 <- s;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__RSA____RSAVP1 <- (trace_h__RSA____RSAVP1 ++ tmp__trace);
    trace_h__RSA____RSAVP1 <-
    (trace_h__RSA____RSAVP1 ++
    [(Assert, (BArray256.is_init b_result 0 256))]);
    x <- result;
    trace_h__RSA____RSAVP1 <-
    (trace_h__RSA____RSAVP1 ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 1032) <= 1064)))]);
    b_ctx_n <- (SBArray1064_1032.get_sub64 b_pk 0);
    ctx_n <- (SBArray1064_1032.get_sub64 pk 0);
    param_1 <- x;
    b_param_0 <- b_ctx_n;
    param_2 <- ctx_n;
    (aux_1, aux_2, tmp__trace) <@ h__FPM___toM_ (param_1,
    (BArray256.init_arr (W8.of_int 255)), param_2, b_param_0);
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__RSA____RSAVP1 <- (trace_h__RSA____RSAVP1 ++ tmp__trace);
    trace_h__RSA____RSAVP1 <-
    (trace_h__RSA____RSAVP1 ++
    [(Assert, (BArray256.is_init b_result_0 0 256))]);
    x <- result_0;
    b_pk <- (BArray1064.init_arr (W8.of_int 255));
    pk <- _pk;
    trace_h__RSA____RSAVP1 <-
    (trace_h__RSA____RSAVP1 ++
    [(Assert, ((0 <= (129 * 8)) /\ (((129 * 8) + 32) <= 1064)))]);
    b_e <- (SBArray1064_32.get_sub64 b_pk 129);
    e <- (SBArray1064_32.get_sub64 pk 129);
    trace_h__RSA____RSAVP1 <-
    (trace_h__RSA____RSAVP1 ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 1032) <= 1064)))]);
    b_ctx_n <- (SBArray1064_1032.get_sub64 b_pk 0);
    ctx_n <- (SBArray1064_1032.get_sub64 pk 0);
    b_param_1 <- b_y;
    param_3 <- y;
    param_4 <- x;
    b_param_2 <- b_e;
    param_5 <- e;
    b_param_3 <- b_ctx_n;
    param_6 <- ctx_n;
    (aux_3, aux_4, tmp__trace) <@ h__FPM__EXPE___expmLR_noct_ (param_3,
    b_param_1, param_4, (BArray256.init_arr (W8.of_int 255)), param_5,
    b_param_2, param_6, b_param_3);
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_h__RSA____RSAVP1 <- (trace_h__RSA____RSAVP1 ++ tmp__trace);
    trace_h__RSA____RSAVP1 <-
    (trace_h__RSA____RSAVP1 ++
    [(Assert, (BArray256.is_init b_result_1 0 256))]);
    y <- result_1;
    b_pk <- (BArray1064.init_arr (W8.of_int 255));
    pk <- _pk;
    trace_h__RSA____RSAVP1 <-
    (trace_h__RSA____RSAVP1 ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 1032) <= 1064)))]);
    b_ctx_n <- (SBArray1064_1032.get_sub64 b_pk 0);
    ctx_n <- (SBArray1064_1032.get_sub64 pk 0);
    param_7 <- y;
    b_param_4 <- b_ctx_n;
    param_8 <- ctx_n;
    (aux_5, aux_6, tmp__trace) <@ h__FPM___fromM_ (param_7,
    (BArray256.init_arr (W8.of_int 255)), param_8, b_param_4);
    result_2 <- aux_5;
    b_result_2 <- aux_6;
    trace_h__RSA____RSAVP1 <- (trace_h__RSA____RSAVP1 ++ tmp__trace);
    trace_h__RSA____RSAVP1 <-
    (trace_h__RSA____RSAVP1 ++
    [(Assert, (BArray256.is_init b_result_2 0 256))]);
    y <- result_2;
    b_y <- (BArray256.init_arr (W8.of_int 255));
    return (y, b_y, trace_h__RSA____RSAVP1);
  }
  proc h__RSA___crt_exp (r:BArray128.t, b_r:BArray128.t, c:BArray256.t,
                         b_c:BArray256.t, dX:BArray128.t, b_dX:BArray128.t,
                         ctxX:BArray520.t, b_ctxX:BArray520.t) : BArray128.t *
                                                                 BArray128.t *
                                                                 trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux_2:BArray128.t;
    var aux_3:BArray128.t;
    var aux_4:BArray128.t;
    var aux_5:BArray128.t;
    var aux_6:BArray128.t;
    var b_cX:BArray128.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var cX:BArray128.t;
    var param_0:BArray256.t;
    var param_1:BArray520.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var param_2:BArray128.t;
    var param_3:BArray520.t;
    var result_0:BArray128.t;
    var b_result_0:BArray128.t;
    var param_4:BArray128.t;
    var param_5:BArray520.t;
    var result_1:BArray128.t;
    var b_result_1:BArray128.t;
    var b_param_0:BArray128.t;
    var param_6:BArray128.t;
    var param_7:BArray128.t;
    var param_8:BArray128.t;
    var param_9:BArray520.t;
    var result_2:BArray128.t;
    var b_result_2:BArray128.t;
    var trace_h__RSA___crt_exp:trace;
    b_cX <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    cX <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_9 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    trace_h__RSA___crt_exp <- [];
    trace_h__RSA___crt_exp <-
    (trace_h__RSA___crt_exp ++
    [(Assert,
     (((BArray256.is_init b_c 0 256) /\ (BArray128.is_init b_dX 0 128)) /\
     (BArray520.is_init b_ctxX 0 520)))]);
    b_cX <- (BArray128.init_arr (W8.of_int 0));
    b_param <- b_cX;
    param <- cX;
    param_0 <- c;
    param_1 <- ctxX;
    (aux, aux_0, tmp__trace) <@ h__H__FPM___redM_ (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray520.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__RSA___crt_exp <- (trace_h__RSA___crt_exp ++ tmp__trace);
    trace_h__RSA___crt_exp <-
    (trace_h__RSA___crt_exp ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    cX <- result;
    param_2 <- cX;
    param_3 <- ctxX;
    (aux_1, aux_2, tmp__trace) <@ h__H__FPM___toM_ (param_2,
    (BArray128.init_arr (W8.of_int 255)), param_3,
    (BArray520.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__RSA___crt_exp <- (trace_h__RSA___crt_exp ++ tmp__trace);
    trace_h__RSA___crt_exp <-
    (trace_h__RSA___crt_exp ++
    [(Assert, (BArray128.is_init b_result_0 0 128))]);
    cX <- result_0;
    param_4 <- cX;
    param_5 <- ctxX;
    (aux_3, aux_4, tmp__trace) <@ h__H__FPM___toM_ (param_4,
    (BArray128.init_arr (W8.of_int 255)), param_5,
    (BArray520.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_h__RSA___crt_exp <- (trace_h__RSA___crt_exp ++ tmp__trace);
    trace_h__RSA___crt_exp <-
    (trace_h__RSA___crt_exp ++
    [(Assert, (BArray128.is_init b_result_1 0 128))]);
    cX <- result_1;
    b_param_0 <- b_r;
    param_6 <- r;
    param_7 <- cX;
    param_8 <- dX;
    param_9 <- ctxX;
    (aux_5, aux_6, tmp__trace) <@ h__H__FPM__EXP___expmW_ (param_6,
    b_param_0, param_7, (BArray128.init_arr (W8.of_int 255)), param_8,
    (BArray128.init_arr (W8.of_int 255)), param_9,
    (BArray520.init_arr (W8.of_int 255)));
    result_2 <- aux_5;
    b_result_2 <- aux_6;
    trace_h__RSA___crt_exp <- (trace_h__RSA___crt_exp ++ tmp__trace);
    trace_h__RSA___crt_exp <-
    (trace_h__RSA___crt_exp ++
    [(Assert, (BArray128.is_init b_result_2 0 128))]);
    r <- result_2;
    b_r <- (BArray128.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__RSA___crt_exp);
  }
  proc h__RSA____RSASP1_crt (s:BArray256.t, b_s:BArray256.t, sk:BArray1424.t,
                             b_sk:BArray1424.t) : BArray256.t * BArray256.t *
                                                  trace = {
    var aux:BArray128.t;
    var aux_0:BArray128.t;
    var aux_1:BArray128.t;
    var aux_2:BArray128.t;
    var aux_3:BArray128.t;
    var aux_4:BArray128.t;
    var aux_5:BArray128.t;
    var aux_6:BArray128.t;
    var aux_7:BArray128.t;
    var aux_8:BArray128.t;
    var aux_9:BArray128.t;
    var aux_10:BArray128.t;
    var aux_11:BArray128.t;
    var aux_12:BArray128.t;
    var aux_15:BArray128.t;
    var aux_16:BArray128.t;
    var aux_13:BArray256.t;
    var aux_14:BArray256.t;
    var aux_18:BArray256.t;
    var aux_19:BArray256.t;
    var aux_17:bool;
    var b__sP:BArray128.t;
    var b_tmp:BArray256.t;
    var b__t:BArray128.t;
    var _s:BArray256.t;
    var _sk:BArray1424.t;
    var b_x:BArray128.t;
    var x:BArray128.t;
    var _sP:BArray128.t;
    var b_y:BArray128.t;
    var y:BArray128.t;
    var b_ctx:BArray520.t;
    var ctx:BArray520.t;
    var b_param:BArray128.t;
    var param:BArray128.t;
    var param_0:BArray256.t;
    var b_param_0:BArray128.t;
    var param_1:BArray128.t;
    var b_param_1:BArray520.t;
    var param_2:BArray520.t;
    var result:BArray128.t;
    var b_result:BArray128.t;
    var tmp:BArray256.t;
    var b_param_2:BArray128.t;
    var param_3:BArray128.t;
    var param_4:BArray256.t;
    var b_param_3:BArray128.t;
    var param_5:BArray128.t;
    var b_param_4:BArray520.t;
    var param_6:BArray520.t;
    var result_0:BArray128.t;
    var b_result_0:BArray128.t;
    var param_7:BArray128.t;
    var b_param_5:BArray520.t;
    var param_8:BArray520.t;
    var result_1:BArray128.t;
    var b_result_1:BArray128.t;
    var _t:BArray128.t;
    var b_param_6:BArray128.t;
    var param_9:BArray128.t;
    var b_param_7:BArray128.t;
    var param_10:BArray128.t;
    var result_2:BArray128.t;
    var b_result_2:BArray128.t;
    var param_11:BArray128.t;
    var b_param_8:BArray520.t;
    var param_12:BArray520.t;
    var result_3:BArray128.t;
    var b_result_3:BArray128.t;
    var param_13:BArray128.t;
    var param_14:BArray128.t;
    var b_param_9:BArray520.t;
    var param_15:BArray520.t;
    var result_4:BArray128.t;
    var b_result_4:BArray128.t;
    var param_16:BArray128.t;
    var b_param_10:BArray128.t;
    var param_17:BArray128.t;
    var b_param_11:BArray520.t;
    var param_18:BArray520.t;
    var result_5:BArray128.t;
    var b_result_5:BArray128.t;
    var param_19:BArray256.t;
    var param_20:BArray128.t;
    var b_param_12:BArray128.t;
    var param_21:BArray128.t;
    var result_6:BArray256.t;
    var b_result_6:BArray256.t;
    var b_param_13:BArray128.t;
    var param_22:BArray128.t;
    var result_7:BArray128.t;
    var b_result_7:BArray128.t;
    var param_23:BArray256.t;
    var b_param_14:BArray256.t;
    var param_24:BArray256.t;
    var result_8:bool;
    var result_9:BArray256.t;
    var b_result_8:BArray256.t;
    var trace_h__RSA____RSASP1_crt:trace;
    _s <- witness;
    _sP <- witness;
    _sk <- witness;
    _t <- witness;
    b__sP <- witness;
    b__t <- witness;
    b_ctx <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    b_param_7 <- witness;
    b_param_8 <- witness;
    b_param_9 <- witness;
    b_param_10 <- witness;
    b_param_11 <- witness;
    b_param_12 <- witness;
    b_param_13 <- witness;
    b_param_14 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_result_5 <- witness;
    b_result_6 <- witness;
    b_result_7 <- witness;
    b_result_8 <- witness;
    b_tmp <- witness;
    b_x <- witness;
    b_y <- witness;
    ctx <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_9 <- witness;
    param_10 <- witness;
    param_11 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    param_14 <- witness;
    param_15 <- witness;
    param_16 <- witness;
    param_17 <- witness;
    param_18 <- witness;
    param_19 <- witness;
    param_20 <- witness;
    param_21 <- witness;
    param_22 <- witness;
    param_23 <- witness;
    param_24 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_4 <- witness;
    result_5 <- witness;
    result_6 <- witness;
    result_7 <- witness;
    result_9 <- witness;
    tmp <- witness;
    x <- witness;
    y <- witness;
    trace_h__RSA____RSASP1_crt <- [];
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++ [(Assert, (BArray256.is_init b_s 0 256))]);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, (BArray1424.is_init b_sk 0 1424))]);
    b__sP <- (BArray128.init_arr (W8.of_int 0));
    b_tmp <- (BArray256.init_arr (W8.of_int 0));
    b__t <- (BArray128.init_arr (W8.of_int 0));
    _s <- s;
    _sk <- sk;
    b_x <- b__sP;
    x <- _sP;
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, ((0 <= (130 * 8)) /\ (((130 * 8) + 128) <= 1424)))]);
    b_y <- (SBArray1424_128.get_sub64 b_sk 130);
    y <- (SBArray1424_128.get_sub64 sk 130);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 520) <= 1424)))]);
    b_ctx <- (SBArray1424_520.get_sub64 b_sk 0);
    ctx <- (SBArray1424_520.get_sub64 sk 0);
    b_param <- b_x;
    param <- x;
    param_0 <- s;
    b_param_0 <- b_y;
    param_1 <- y;
    b_param_1 <- b_ctx;
    param_2 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__RSA___crt_exp (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)), param_1, b_param_0, param_2,
    b_param_1);
    result <- aux;
    b_result <- aux_0;
    trace_h__RSA____RSASP1_crt <- (trace_h__RSA____RSASP1_crt ++ tmp__trace);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, (BArray128.is_init b_result 0 128))]);
    x <- result;
    _sP <- x;
    s <- _s;
    b_sk <- (BArray1424.init_arr (W8.of_int 255));
    sk <- _sk;
    b_x <- (SBArray256_128.get_sub64 b_tmp 0);
    x <- (SBArray256_128.get_sub64 tmp 0);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, ((0 <= (146 * 8)) /\ (((146 * 8) + 128) <= 1424)))]);
    b_y <- (SBArray1424_128.get_sub64 b_sk 146);
    y <- (SBArray1424_128.get_sub64 sk 146);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, ((0 <= (65 * 8)) /\ (((65 * 8) + 520) <= 1424)))]);
    b_ctx <- (SBArray1424_520.get_sub64 b_sk 65);
    ctx <- (SBArray1424_520.get_sub64 sk 65);
    b_param_2 <- b_x;
    param_3 <- x;
    param_4 <- s;
    b_param_3 <- b_y;
    param_5 <- y;
    b_param_4 <- b_ctx;
    param_6 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__RSA___crt_exp (param_3, b_param_2,
    param_4, (BArray256.init_arr (W8.of_int 255)), param_5, b_param_3,
    param_6, b_param_4);
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__RSA____RSASP1_crt <- (trace_h__RSA____RSASP1_crt ++ tmp__trace);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, (BArray128.is_init b_result_0 0 128))]);
    x <- result_0;
    b_sk <- (BArray1424.init_arr (W8.of_int 255));
    sk <- _sk;
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, ((0 <= (65 * 8)) /\ (((65 * 8) + 520) <= 1424)))]);
    b_ctx <- (SBArray1424_520.get_sub64 b_sk 65);
    ctx <- (SBArray1424_520.get_sub64 sk 65);
    param_7 <- x;
    b_param_5 <- b_ctx;
    param_8 <- ctx;
    (aux_3, aux_4, tmp__trace) <@ h__H__FPM___fromM_ (param_7,
    (BArray128.init_arr (W8.of_int 255)), param_8, b_param_5);
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_h__RSA____RSASP1_crt <- (trace_h__RSA____RSASP1_crt ++ tmp__trace);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, (BArray128.is_init b_result_1 0 128))]);
    x <- result_1;
    b_tmp <-
    (SBArray256_128.set_sub64 b_tmp 0 (BArray128.init_arr (W8.of_int 255)));
    tmp <- (SBArray256_128.set_sub64 tmp 0 x);
    b_y <- b__t;
    y <- _t;
    b_x <- (SBArray256_128.get_sub64 b_tmp 0);
    x <- (SBArray256_128.get_sub64 tmp 0);
    b_param_6 <- b_y;
    param_9 <- y;
    b_param_7 <- b_x;
    param_10 <- x;
    (aux_5, aux_6, tmp__trace) <@ h__H__BN___mov_ (param_9, b_param_6,
    param_10, b_param_7);
    result_2 <- aux_5;
    b_result_2 <- aux_6;
    trace_h__RSA____RSASP1_crt <- (trace_h__RSA____RSASP1_crt ++ tmp__trace);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, (BArray128.is_init b_result_2 0 128))]);
    y <- result_2;
    b_sk <- (BArray1424.init_arr (W8.of_int 255));
    sk <- _sk;
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 520) <= 1424)))]);
    b_ctx <- (SBArray1424_520.get_sub64 b_sk 0);
    ctx <- (SBArray1424_520.get_sub64 sk 0);
    param_11 <- y;
    b_param_8 <- b_ctx;
    param_12 <- ctx;
    (aux_7, aux_8, tmp__trace) <@ h__H__FPM___toM_ (param_11,
    (BArray128.init_arr (W8.of_int 255)), param_12, b_param_8);
    result_3 <- aux_7;
    b_result_3 <- aux_8;
    trace_h__RSA____RSASP1_crt <- (trace_h__RSA____RSASP1_crt ++ tmp__trace);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, (BArray128.is_init b_result_3 0 128))]);
    y <- result_3;
    x <- _sP;
    b_sk <- (BArray1424.init_arr (W8.of_int 255));
    sk <- _sk;
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 520) <= 1424)))]);
    b_ctx <- (SBArray1424_520.get_sub64 b_sk 0);
    ctx <- (SBArray1424_520.get_sub64 sk 0);
    param_13 <- x;
    param_14 <- y;
    b_param_9 <- b_ctx;
    param_15 <- ctx;
    (aux_9, aux_10, tmp__trace) <@ h__H__FPM___submU_ (param_13,
    (BArray128.init_arr (W8.of_int 255)), param_14,
    (BArray128.init_arr (W8.of_int 255)), param_15, b_param_9);
    result_4 <- aux_9;
    b_result_4 <- aux_10;
    trace_h__RSA____RSASP1_crt <- (trace_h__RSA____RSASP1_crt ++ tmp__trace);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, (BArray128.is_init b_result_4 0 128))]);
    x <- result_4;
    b_sk <- (BArray1424.init_arr (W8.of_int 255));
    sk <- _sk;
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, ((0 <= (162 * 8)) /\ (((162 * 8) + 128) <= 1424)))]);
    b_y <- (SBArray1424_128.get_sub64 b_sk 162);
    y <- (SBArray1424_128.get_sub64 sk 162);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 520) <= 1424)))]);
    b_ctx <- (SBArray1424_520.get_sub64 b_sk 0);
    ctx <- (SBArray1424_520.get_sub64 sk 0);
    param_16 <- x;
    b_param_10 <- b_y;
    param_17 <- y;
    b_param_11 <- b_ctx;
    param_18 <- ctx;
    (aux_11, aux_12, tmp__trace) <@ h__H__FPM___mulmU_ (param_16,
    (BArray128.init_arr (W8.of_int 255)), param_17, b_param_10, param_18,
    b_param_11);
    result_5 <- aux_11;
    b_result_5 <- aux_12;
    trace_h__RSA____RSASP1_crt <- (trace_h__RSA____RSASP1_crt ++ tmp__trace);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, (BArray128.is_init b_result_5 0 128))]);
    x <- result_5;
    _sP <- x;
    s <- _s;
    b_sk <- (BArray1424.init_arr (W8.of_int 255));
    sk <- _sk;
    x <- _sP;
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, ((0 <= (65 * 8)) /\ (((65 * 8) + 128) <= 1424)))]);
    b_y <- (SBArray1424_128.get_sub64 b_sk 65);
    y <- (SBArray1424_128.get_sub64 sk 65);
    param_19 <- s;
    param_20 <- x;
    b_param_12 <- b_y;
    param_21 <- y;
    (aux_13, aux_14, tmp__trace) <@ h__H__MUL___muln_ (param_19,
    (BArray256.init_arr (W8.of_int 255)), param_20,
    (BArray128.init_arr (W8.of_int 255)), param_21, b_param_12);
    result_6 <- aux_13;
    b_result_6 <- aux_14;
    trace_h__RSA____RSASP1_crt <- (trace_h__RSA____RSASP1_crt ++ tmp__trace);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, (BArray256.is_init b_result_6 0 256))]);
    s <- result_6;
    _s <- s;
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 256)))]);
    b_x <- (SBArray256_128.get_sub64 b_tmp 16);
    x <- (SBArray256_128.get_sub64 tmp 16);
    b_param_13 <- b_x;
    param_22 <- x;
    (aux_15, aux_16, tmp__trace) <@ h__H__BN___set0_ (param_22, b_param_13);
    result_7 <- aux_15;
    b_result_7 <- aux_16;
    trace_h__RSA____RSASP1_crt <- (trace_h__RSA____RSASP1_crt ++ tmp__trace);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, (BArray128.is_init b_result_7 0 128))]);
    x <- result_7;
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, ((0 <= (16 * 8)) /\ (((16 * 8) + 128) <= 256)))]);
    b_tmp <-
    (SBArray256_128.set_sub64 b_tmp 16 (BArray128.init_arr (W8.of_int 255)));
    tmp <- (SBArray256_128.set_sub64 tmp 16 x);
    s <- _s;
    param_23 <- s;
    b_param_14 <- b_tmp;
    param_24 <- tmp;
    (aux_17, aux_18, aux_19, tmp__trace) <@ h__BN___addU_ (param_23,
    (BArray256.init_arr (W8.of_int 255)), param_24, b_param_14);
    result_8 <- aux_17;
    result_9 <- aux_18;
    b_result_8 <- aux_19;
    trace_h__RSA____RSASP1_crt <- (trace_h__RSA____RSASP1_crt ++ tmp__trace);
    trace_h__RSA____RSASP1_crt <-
    (trace_h__RSA____RSASP1_crt ++
    [(Assert, (BArray256.is_init b_result_8 0 256))]);
    s <- result_9;
    b_s <- (BArray256.init_arr (W8.of_int 255));
    return (s, b_s, trace_h__RSA____RSASP1_crt);
  }
  proc rsa_init (pk:BArray1064.t, b_pk:BArray1064.t, sk:BArray1424.t,
                 b_sk:BArray1424.t) : BArray1064.t * BArray1064.t *
                                      BArray1424.t * BArray1424.t * trace = {
    var aux:BArray1064.t;
    var aux_0:BArray1064.t;
    var aux_1:BArray1424.t;
    var aux_2:BArray1424.t;
    var b__sk:BArray1424.t;
    var _sk:BArray1424.t;
    var kp:BArray288.t;
    var b_param:BArray1064.t;
    var param:BArray1064.t;
    var param_0:BArray288.t;
    var result:BArray1064.t;
    var b_result:BArray1064.t;
    var _pk:BArray1064.t;
    var ks:BArray640.t;
    var b_param_0:BArray1424.t;
    var param_1:BArray1424.t;
    var param_2:BArray640.t;
    var result_0:BArray1424.t;
    var b_result_0:BArray1424.t;
    var trace_rsa_init:trace;
    _pk <- witness;
    _sk <- witness;
    b__sk <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    kp <- witness;
    ks <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_rsa_init <- [];
    b__sk <- b_sk;
    _sk <- sk;
    kp <- pk_test;
    b_param <- b_pk;
    param <- pk;
    param_0 <- kp;
    (aux, aux_0, tmp__trace) <@ h__RSA____RSA_expand_pk (param, b_param,
    param_0, (BArray288.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_rsa_init <- (trace_rsa_init ++ tmp__trace);
    trace_rsa_init <-
    (trace_rsa_init ++ [(Assert, (BArray1064.is_init b_result 0 1064))]);
    pk <- result;
    _pk <- pk;
    b_sk <- b__sk;
    sk <- _sk;
    ks <- sk_test;
    b_param_0 <- b_sk;
    param_1 <- sk;
    param_2 <- ks;
    (aux_1, aux_2, tmp__trace) <@ h__RSA____RSA_expand_sk (param_1,
    b_param_0, param_2, (BArray640.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_rsa_init <- (trace_rsa_init ++ tmp__trace);
    trace_rsa_init <-
    (trace_rsa_init ++ [(Assert, (BArray1424.is_init b_result_0 0 1424))]);
    sk <- result_0;
    pk <- _pk;
    b_pk <- (BArray1064.init_arr (W8.of_int 255));
    b_sk <- (BArray1424.init_arr (W8.of_int 255));
    return (pk, b_pk, sk, b_sk, trace_rsa_init);
  }
  proc rsa_dec (m:BArray256.t, b_m:BArray256.t, c:BArray256.t,
                b_c:BArray256.t, sk:BArray1424.t, b_sk:BArray1424.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var aux_1:BArray256.t;
    var aux_2:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var param_1:BArray256.t;
    var param_2:BArray1424.t;
    var result_0:BArray256.t;
    var b_result_0:BArray256.t;
    var trace_rsa_dec:trace;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_rsa_dec <- [];
    trace_rsa_dec <-
    (trace_rsa_dec ++
    [(Assert,
     ((BArray256.is_init b_c 0 256) /\ (BArray1424.is_init b_sk 0 1424)))]);
    b_param <- b_m;
    param <- m;
    param_0 <- c;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_rsa_dec <- (trace_rsa_dec ++ tmp__trace);
    trace_rsa_dec <-
    (trace_rsa_dec ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    m <- result;
    param_1 <- m;
    param_2 <- sk;
    (aux_1, aux_2, tmp__trace) <@ h__RSA____RSASP1_crt (param_1,
    (BArray256.init_arr (W8.of_int 255)), param_2,
    (BArray1424.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_rsa_dec <- (trace_rsa_dec ++ tmp__trace);
    trace_rsa_dec <-
    (trace_rsa_dec ++ [(Assert, (BArray256.is_init b_result_0 0 256))]);
    m <- result_0;
    b_m <- (BArray256.init_arr (W8.of_int 255));
    return (m, b_m, trace_rsa_dec);
  }
  proc rsa_enc (c:BArray256.t, b_c:BArray256.t, m:BArray256.t,
                b_m:BArray256.t, pk:BArray1064.t, b_pk:BArray1064.t) : 
  BArray256.t * BArray256.t * trace = {
    var aux:BArray256.t;
    var aux_0:BArray256.t;
    var b_param:BArray256.t;
    var param:BArray256.t;
    var param_0:BArray256.t;
    var param_1:BArray1064.t;
    var result:BArray256.t;
    var b_result:BArray256.t;
    var trace_rsa_enc:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_rsa_enc <- [];
    trace_rsa_enc <-
    (trace_rsa_enc ++
    [(Assert,
     ((BArray256.is_init b_m 0 256) /\ (BArray1064.is_init b_pk 0 1064)))]);
    b_param <- b_c;
    param <- c;
    param_0 <- m;
    param_1 <- pk;
    (aux, aux_0, tmp__trace) <@ h__RSA____RSAVP1 (param, b_param, param_0,
    (BArray256.init_arr (W8.of_int 255)), param_1,
    (BArray1064.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_rsa_enc <- (trace_rsa_enc ++ tmp__trace);
    trace_rsa_enc <-
    (trace_rsa_enc ++ [(Assert, (BArray256.is_init b_result 0 256))]);
    c <- result;
    b_c <- (BArray256.init_arr (W8.of_int 255));
    return (c, b_c, trace_rsa_enc);
  }
}.

(* The post and trace are valid. *)

op uTIL____mask_cf_spec _mask =
   hoare [M.uTIL____mask_cf :
   ((_mask = mask) /\ true) ==> (true /\ (valid res.`2))].

op uTIL____cf_mask_spec _cf =
   hoare [M.uTIL____cf_mask :
   ((_cf = cf) /\ true) ==> (true /\ (valid res.`2))].

op uTIL____addacc3_spec _a _b_a _b1 _b0 _k =
   hoare [M.uTIL____addacc3 :
   (((_k = k) /\ ((_b0 = b0) /\ ((_b1 = b1) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   (BArray24.is_init _b_a 0 24)) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

op uTIL____addacc3x2_spec _a _b_a _x _y _k =
   hoare [M.uTIL____addacc3x2 :
   (((_k = k) /\ ((_y = y) /\ ((_x = x) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   (BArray24.is_init _b_a 0 24)) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

op h__H__BN____mov_spec _r _b_r _a _b_a =
   hoare [M.h__H__BN____mov :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__BN___mov_spec _r _b_r _a _b_a =
   hoare [M.h__H__BN___mov :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__BN___mov__spec _r _b_r _a _b_a =
   hoare [M.h__H__BN___mov_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__BN____cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.h__H__BN____cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray128.is_init _b_b 0 128) /\ (BArray128.is_init _b_a 0 128))) ==>
   ((BArray128.is_init res.`2 0 128) /\ (valid res.`3))].

op h__H__BN___cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.h__H__BN___cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray128.is_init _b_b 0 128) /\ (BArray128.is_init _b_a 0 128))) ==>
   ((BArray128.is_init res.`2 0 128) /\ (valid res.`3))].

op h__H__BN___cmov__spec _a _b_a _cond _b _b_b =
   hoare [M.h__H__BN___cmov_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray128.is_init _b_b 0 128) /\ (BArray128.is_init _b_a 0 128))) ==>
   ((BArray128.is_init res.`2 0 128) /\ (valid res.`3))].

op h__H__BN____fill_spec _a _b_a _x =
   hoare [M.h__H__BN____fill :
   (((_x = x) /\ ((_b_a = b_a) /\ (_a = a))) /\ true) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__BN___fill__spec _a _b_a _x =
   hoare [M.h__H__BN___fill_ :
   (((_x = x) /\ ((_b_a = b_a) /\ (_a = a))) /\ true) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__BN___set0__spec _a _b_a =
   hoare [M.h__H__BN___set0_ :
   (((_b_a = b_a) /\ (_a = a)) /\ true) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__BN____addc1_spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__H__BN____addc1 :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray128.is_init _b_r 0 8) /\ (BArray128.is_init _b_a 0 (8 * 16))) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray128.is_init res.`3 0 (8 * 16)) /\ (valid res.`4))].

op h__H__BN___addc1_spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__H__BN___addc1 :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray128.is_init _b_r 0 8) /\ (BArray128.is_init _b_a 0 (8 * 16))) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray128.is_init res.`3 0 (8 * 16)) /\ (valid res.`4))].

op h__H__BN___addc1__spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__H__BN___addc1_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray128.is_init _b_r 0 8) /\ (BArray128.is_init _b_a 0 (8 * 16))) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray128.is_init res.`3 0 (8 * 16)) /\ (valid res.`4))].

op h__H__BN___add__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__BN___add_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray128.is_init res.`3 0 (8 * 16)) /\ (valid res.`4))].

op h__H__BN____subc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__H__BN____subc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray128.is_init _b_b 0 128) /\ (BArray128.is_init _b_a 0 128))) ==>
   ((BArray128.is_init res.`3 0 128) /\ (valid res.`4))].

op h__H__BN___subc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__H__BN___subc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray128.is_init _b_b 0 128) /\ (BArray128.is_init _b_a 0 128))) ==>
   ((BArray128.is_init res.`3 0 128) /\ (valid res.`4))].

op h__H__BN___subc1U__spec _a _b_a _b _b_b _cf =
   hoare [M.h__H__BN___subc1U_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray128.is_init _b_b 0 128) /\ (BArray128.is_init _b_a 0 128))) ==>
   ((BArray128.is_init res.`3 0 128) /\ (valid res.`4))].

op h__H__BN___subU__spec _a _b_a _b _b_b =
   hoare [M.h__H__BN___subU_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray128.is_init _b_b 0 128) /\ (BArray128.is_init _b_a 0 128))) ==>
   ((BArray128.is_init res.`3 0 128) /\ (valid res.`4))].

op h__H__BN____negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.h__H__BN____negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray128.is_init _b_r 0 8) /\ (BArray128.is_init _b_a 0 (8 * 16)))) ==>
   ((BArray128.is_init res.`3 0 (8 * 16)) /\ (valid res.`4))].

op h__H__BN___negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.h__H__BN___negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray128.is_init _b_r 0 8) /\ (BArray128.is_init _b_a 0 (8 * 16)))) ==>
   ((BArray128.is_init res.`3 0 (8 * 16)) /\ (valid res.`4))].

op h__H__BN___negc1__spec _r _b_r _a _b_a _cf =
   hoare [M.h__H__BN___negc1_ :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray128.is_init _b_r 0 8) /\ (BArray128.is_init _b_a 0 (8 * 16)))) ==>
   ((BArray128.is_init res.`3 0 (8 * 16)) /\ (valid res.`4))].

op h__H__BN___neg__spec _r _b_r _a _b_a =
   hoare [M.h__H__BN___neg_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray128.is_init res.`3 0 (8 * 16)) /\ (valid res.`4))].

op h__H__BN___caddU__spec _x _b_x _cf _y _b_y =
   hoare [M.h__H__BN___caddU_ :
   (((_b_y = b_y) /\
    ((_y = y) /\ ((_cf = cf) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray128.is_init _b_y 0 128) /\ (BArray128.is_init _b_x 0 128))) ==>
   ((BArray128.is_init res.`2 0 128) /\ (valid res.`3))].

op h__H__BN___cminusP__spec _x _b_x _mP _b_mP _lastbit =
   hoare [M.h__H__BN___cminusP_ :
   (((_lastbit = lastbit) /\
    ((_b_mP = b_mP) /\ ((_mP = mP) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray128.is_init _b_mP 0 128) /\ (BArray128.is_init _b_x 0 128))) ==>
   ((BArray128.is_init res.`2 0 128) /\ (valid res.`3))].

op h__H__MUL__UNR____muln_innerloop_spec _x _b_x _k _istart _iend _a _b_a _b _b_b =
   hoare [M.h__H__MUL__UNR____muln_innerloop :
   (((_b_b = b_b) /\
    ((_b = b) /\
    ((_b_a = b_a) /\
    ((_a = a) /\
    ((_iend = iend) /\
    ((_istart = istart) /\ ((_k = k) /\ ((_b_x = b_x) /\ (_x = x))))))))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((((((0 <= _istart) /\ (_iend <= 16)) /\ (0 <= (_k - (_iend - 1)))) /\
      ((_k - _istart) < 16)) /\
     (BArray24.is_init _b_x 0 24)) /\
    (BArray128.is_init _b_a (8 * _istart) (8 * (_iend - _istart)))) /\
   (BArray128.is_init _b_b 0 (8 * 16))))))))))))) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

op h__H__MUL__UNR____ps_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL__UNR____ps_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__UNR___ps_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL__UNR___ps_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__UNR___ps_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL__UNR___ps_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__UNR____sqrn_innerloop_spec _x _b_x _k _istart _iend _a _b_a =
   hoare [M.h__H__MUL__UNR____sqrn_innerloop :
   (((_b_a = b_a) /\
    ((_a = a) /\
    ((_iend = iend) /\
    ((_istart = istart) /\ ((_k = k) /\ ((_b_x = b_x) /\ (_x = x))))))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   ((((((0 <= _istart) /\ (_iend <= 16)) /\ (0 <= (_k - (_iend - 1)))) /\
     ((_k - _istart) < 16)) /\
    (BArray24.is_init _b_x 0 24)) /\
   (BArray128.is_init _b_a 0 (8 * 16)))))))))) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

op h__H__MUL__UNR____ps_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL__UNR____ps_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__UNR___ps_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL__UNR___ps_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__UNR___ps_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL__UNR___ps_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__UNR____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__H__MUL__UNR____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray256.is_init _b_a 0 (16 * 16)) /\
   (BArray256.is_init _b__P_mP 0 (16 * 16)))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__MUL__LOOP____mul1_spec _r _b_r _a _b _b_b =
   hoare [M.h__H__MUL__LOOP____mul1 :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray128.is_init _b_b 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (8 * (16 + 1))) /\ (valid res.`3))].

op h__H__MUL__LOOP____mul1acc_spec _k _r _b_r _a _b _b_b =
   hoare [M.h__H__MUL__LOOP____mul1acc :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= (W64.to_uint _k)) /\ ((W64.to_uint _k) < 16)) /\
    (BArray256.is_init _b_r 0 (8 * ((W64.to_uint _k) + 16)))) /\
   (BArray128.is_init _b_b 0 (8 * 16))))))) ==>
   ((true /\
    (BArray256.is_init res.`2 0 (8 * (((W64.to_uint _k) + 16) + 1)))) /\
   (valid res.`3))].

op h__H__MUL__LOOP___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL__LOOP___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__LOOP___os_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL__LOOP___os_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__LOOP___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL__LOOP___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__LOOP___os_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL__LOOP___os_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__LOOP____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__H__MUL__LOOP____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray256.is_init _b_a 0 (16 * 16)) /\
   (BArray256.is_init _b__P_mP 0 (16 * 16)))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__MUL__XUNR____mul1_spec _r _b_r _a _b _b_b =
   hoare [M.h__H__MUL__XUNR____mul1 :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray128.is_init _b_b 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (8 * (16 + 1))) /\ (valid res.`3))].

op h__H__MUL__XUNR____mul1acc_spec _k _r _b_r _a _b _b_b =
   hoare [M.h__H__MUL__XUNR____mul1acc :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _k) /\ (_k < 16)) /\ (BArray256.is_init _b_r 0 (8 * (_k + 16)))) /\
   (BArray128.is_init _b_b 0 (8 * 16))))))) ==>
   ((true /\ (BArray256.is_init res.`2 0 (8 * ((_k + 16) + 1)))) /\
   (valid res.`3))].

op h__H__MUL__XUNR___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL__XUNR___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XUNR___os_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL__XUNR___os_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XUNR____sqr_row0_spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL__XUNR____sqr_row0 :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   ((2 <= 16) /\ (BArray128.is_init _b_a 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 8 (8 * 16)) /\ (valid res.`3))].

op h__H__MUL__XUNR____sqr_rowacc_spec _i _r _b_r _a _b_a =
   hoare [M.h__H__MUL__XUNR____sqr_rowacc :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_i = i))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _i) /\ (_i < (16 - 1))) /\
    (BArray256.is_init _b_r 8 (8 * ((_i + 16) - 1)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))))))) ==>
   ((true /\ (BArray256.is_init res.`2 8 (8 * (_i + 16)))) /\ (valid res.`3))].

op h__H__MUL__XUNR____sqr_diag_spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL__XUNR____sqr_diag :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (((2 <= 16) /\ (BArray256.is_init _b_r 8 (8 * ((2 * 16) - 2)))) /\
   (BArray128.is_init _b_a 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XUNR___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL__XUNR___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XUNR___os_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL__XUNR___os_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XUNR____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__H__MUL__XUNR____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray256.is_init _b_a 0 (16 * 16)) /\
   (BArray256.is_init _b__P_mP 0 (16 * 16)))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__MUL__XLOOP____mul1_spec _r _b_r _a _b _b_b =
   hoare [M.h__H__MUL__XLOOP____mul1 :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray128.is_init _b_b 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (8 * (16 + 1))) /\ (valid res.`3))].

op h__H__MUL__XLOOP____mul1acc_spec _k _r _b_r _a _b _b_b =
   hoare [M.h__H__MUL__XLOOP____mul1acc :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= (W64.to_uint _k)) /\ ((W64.to_uint _k) < 16)) /\
    (BArray256.is_init _b_r 0 (8 * ((W64.to_uint _k) + 16)))) /\
   (BArray128.is_init _b_b 0 (8 * 16))))))) ==>
   ((true /\
    (BArray256.is_init res.`2 0 (8 * (((W64.to_uint _k) + 16) + 1)))) /\
   (valid res.`3))].

op h__H__MUL__XLOOP___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL__XLOOP___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XLOOP___os_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL__XLOOP___os_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XLOOP___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL__XLOOP___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XLOOP___os_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL__XLOOP___os_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XLOOP____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__H__MUL__XLOOP____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray256.is_init _b_a 0 (16 * 16)) /\
   (BArray256.is_init _b__P_mP 0 (16 * 16)))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__MUL__XREG____mulr_row0_spec _a _b _b_b =
   hoare [M.h__H__MUL__XREG____mulr_row0 :
   (((_b_b = b_b) /\ ((_b = b) /\ (_a = a))) /\
   (BArray128.is_init _b_b 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (8 * (16 + 1))) /\ (valid res.`3))].

op h__H__MUL__XREG____mulr_rowk_spec _k _t _b_t _a _b _b_b =
   hoare [M.h__H__MUL__XREG____mulr_rowk :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_t = b_t) /\ ((_t = t) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _k) /\ (_k < 16)) /\ (BArray256.is_init _b_t 0 (8 * (_k + 16)))) /\
   (BArray128.is_init _b_b 0 (8 * 16))))))) ==>
   ((true /\ (BArray256.is_init res.`2 0 (8 * ((_k + 16) + 1)))) /\
   (valid res.`3))].

op h__H__MUL__XREG___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL__XREG___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XREG___os_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL__XREG___os_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XREG____sqrr_row0_spec _a _b_a =
   hoare [M.h__H__MUL__XREG____sqrr_row0 :
   (((_b_a = b_a) /\ (_a = a)) /\
   ((2 <= 16) /\ (BArray128.is_init _b_a 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 8 (8 * 16)) /\ (valid res.`3))].

op h__H__MUL__XREG____sqrr_rowi_spec _i _t _b_t _a _b_a =
   hoare [M.h__H__MUL__XREG____sqrr_rowi :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_t = b_t) /\ ((_t = t) /\ (_i = i))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _i) /\ (_i < (16 - 1))) /\
    (BArray256.is_init _b_t 8 (8 * ((_i + 16) - 1)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))))))) ==>
   ((true /\ (BArray256.is_init res.`2 8 (8 * (_i + 16)))) /\ (valid res.`3))].

op h__H__MUL__XREG____sqrr_diag_spec _r _b_r _t _b_t _a _b_a =
   hoare [M.h__H__MUL__XREG____sqrr_diag :
   (((_b_a = b_a) /\
    ((_a = a) /\ ((_b_t = b_t) /\ ((_t = t) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((((2 <= 16) /\ (BArray256.is_init _b_r 8 (8 * ((2 * 16) - 10)))) /\
    (BArray256.is_init _b_t 8 (8 * ((2 * 16) - 2)))) /\
   (BArray128.is_init _b_a 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XREG___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL__XREG___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XREG___os_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL__XREG___os_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL__XREG____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__H__MUL__XREG____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray256.is_init _b_a 0 (16 * 16)) /\
   (BArray256.is_init _b__P_mP 0 (16 * 16)))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__MUL___muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL___muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL___sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__H__MUL___sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__MUL____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__H__MUL____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray256.is_init _b_a 0 (16 * 16)) /\
   (BArray256.is_init _b__P_mP 0 (16 * 16)))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__FPM__fun_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__FPM__fun_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray128.is_init _b_a 0 (8 * 16)) /\
   (BArray128.is_init _b_b 0 (8 * 16)))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__FPM__fun_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__H__FPM__fun_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray128.is_init _b_a 0 (8 * 16))) ==>
   ((BArray256.is_init res.`2 0 (16 * 16)) /\ (valid res.`3))].

op h__H__FPM___redM_spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__H__FPM___redM :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (16 * 16)) /\
   (BArray520.is_init _b_ctx 0 (8 * 65)))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__FPM___redM__spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__H__FPM___redM_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (16 * 16)) /\
   (BArray520.is_init _b_ctx 0 (8 * 65)))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__FPM___fromM__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__H__FPM___fromM_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray520.is_init _b_ctx 0 520) /\ (BArray128.is_init _b_a 0 128))) ==>
   ((BArray128.is_init res.`2 0 128) /\ (valid res.`3))].

op h__H__FPM__fun_red_spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__H__FPM__fun_red :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (16 * 16)) /\
   (BArray520.is_init _b_ctx 0 (8 * 65)))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__FPM___addm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__H__FPM___addm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray128.is_init _b_a 0 (8 * 16)) /\
    (BArray128.is_init _b_b 0 (8 * 16))) /\
   (BArray520.is_init _b_ctx (8 * 16) (8 * 16)))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__FPM___submU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__H__FPM___submU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray520.is_init _b_ctx 0 520) /\
   ((BArray128.is_init _b_b 0 128) /\ (BArray128.is_init _b_a 0 128)))) ==>
   ((BArray128.is_init res.`2 0 128) /\ (valid res.`3))].

op h__H__FPM___mulmU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__H__FPM___mulmU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray520.is_init _b_ctx 0 520) /\
   ((BArray128.is_init _b_b 0 128) /\ (BArray128.is_init _b_a 0 128)))) ==>
   ((BArray128.is_init res.`2 0 128) /\ (valid res.`3))].

op h__H__FPM___sqrmU__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__H__FPM___sqrmU_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray520.is_init _b_ctx 0 520) /\ (BArray128.is_init _b_a 0 128))) ==>
   ((BArray128.is_init res.`2 0 128) /\ (valid res.`3))].

op h__H__FPM__fun_mulU_spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__H__FPM__fun_mulU :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray520.is_init _b_ctx 0 520) /\
   ((BArray128.is_init _b_b 0 128) /\ (BArray128.is_init _b_a 0 128)))) ==>
   ((BArray128.is_init res.`2 0 128) /\ (valid res.`3))].

op h__H__FPM__fun_sqrU_spec _a _b_a _ctx _b_ctx =
   hoare [M.h__H__FPM__fun_sqrU :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray520.is_init _b_ctx 0 520) /\ (BArray128.is_init _b_a 0 128))) ==>
   ((BArray128.is_init res.`2 0 128) /\ (valid res.`3))].

op h__H__FPM__EXP____tblsel_spec _r _b_r _tbl _b_tbl _idx =
   hoare [M.h__H__FPM__EXP____tblsel :
   (((_idx = idx) /\
    ((_b_tbl = b_tbl) /\ ((_tbl = tbl) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray2048.is_init _b_tbl 0 (128 * 16))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__FPM__EXP___expmW_spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__H__FPM__EXP___expmW :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray128.is_init _b_a 0 (8 * 16)) /\
    (BArray128.is_init _b_b 0 (8 * 16))) /\
   (BArray520.is_init _b_ctx 0 (8 * 65)))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__FPM__EXP___expmW__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__H__FPM__EXP___expmW_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray128.is_init _b_a 0 (8 * 16)) /\
    (BArray128.is_init _b_b 0 (8 * 16))) /\
   (BArray520.is_init _b_ctx 0 (8 * 65)))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__H__FPM___toM__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__H__FPM___toM_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray520.is_init _b_ctx 0 520) /\ (BArray128.is_init _b_a 0 128))) ==>
   ((BArray128.is_init res.`2 0 128) /\ (valid res.`3))].

op h__H__FPM___ctx_init__spec _ctx _b_ctx _p _b_P =
   hoare [M.h__H__FPM___ctx_init_ :
   (((_b_P = b_P) /\ ((_p = p) /\ ((_b_ctx = b_ctx) /\ (_ctx = ctx)))) /\
   (BArray128.is_init _b_P 0 (8 * 16))) ==>
   ((BArray520.is_init res.`2 0 (8 * 65)) /\ (valid res.`3))].

op h__BN____mov_spec _r _b_r _a _b_a =
   hoare [M.h__BN____mov :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__BN___mov_spec _r _b_r _a _b_a =
   hoare [M.h__BN___mov :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__BN___mov__spec _r _b_r _a _b_a =
   hoare [M.h__BN___mov_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__BN____cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.h__BN____cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray256.is_init _b_b 0 256) /\ (BArray256.is_init _b_a 0 256))) ==>
   ((BArray256.is_init res.`2 0 256) /\ (valid res.`3))].

op h__BN___cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.h__BN___cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray256.is_init _b_b 0 256) /\ (BArray256.is_init _b_a 0 256))) ==>
   ((BArray256.is_init res.`2 0 256) /\ (valid res.`3))].

op h__BN___cmov__spec _a _b_a _cond _b _b_b =
   hoare [M.h__BN___cmov_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray256.is_init _b_b 0 256) /\ (BArray256.is_init _b_a 0 256))) ==>
   ((BArray256.is_init res.`2 0 256) /\ (valid res.`3))].

op h__BN____fill_spec _a _b_a _x =
   hoare [M.h__BN____fill :
   (((_x = x) /\ ((_b_a = b_a) /\ (_a = a))) /\ true) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__BN___fill__spec _a _b_a _x =
   hoare [M.h__BN___fill_ :
   (((_x = x) /\ ((_b_a = b_a) /\ (_a = a))) /\ true) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__BN___set0__spec _a _b_a =
   hoare [M.h__BN___set0_ :
   (((_b_a = b_a) /\ (_a = a)) /\ true) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__BN____addc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN____addc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray256.is_init _b_b 0 256) /\ (BArray256.is_init _b_a 0 256))) ==>
   ((BArray256.is_init res.`3 0 256) /\ (valid res.`4))].

op h__BN___addc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray256.is_init _b_b 0 256) /\ (BArray256.is_init _b_a 0 256))) ==>
   ((BArray256.is_init res.`3 0 256) /\ (valid res.`4))].

op h__BN___addc1U__spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1U_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray256.is_init _b_b 0 256) /\ (BArray256.is_init _b_a 0 256))) ==>
   ((BArray256.is_init res.`3 0 256) /\ (valid res.`4))].

op h__BN___addU__spec _a _b_a _b _b_b =
   hoare [M.h__BN___addU_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray256.is_init _b_b 0 256) /\ (BArray256.is_init _b_a 0 256))) ==>
   ((BArray256.is_init res.`3 0 256) /\ (valid res.`4))].

op h__BN____addc1_spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN____addc1 :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray256.is_init _b_r 0 8) /\ (BArray256.is_init _b_a 0 (8 * 32))) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray256.is_init res.`3 0 (8 * 32)) /\ (valid res.`4))].

op h__BN___addc1_spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1 :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray256.is_init _b_r 0 8) /\ (BArray256.is_init _b_a 0 (8 * 32))) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray256.is_init res.`3 0 (8 * 32)) /\ (valid res.`4))].

op h__BN___addc1__spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray256.is_init _b_r 0 8) /\ (BArray256.is_init _b_a 0 (8 * 32))) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray256.is_init res.`3 0 (8 * 32)) /\ (valid res.`4))].

op h__BN___add__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__BN___add_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray256.is_init res.`3 0 (8 * 32)) /\ (valid res.`4))].

op h__BN____negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.h__BN____negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray256.is_init _b_r 0 8) /\ (BArray256.is_init _b_a 0 (8 * 32)))) ==>
   ((BArray256.is_init res.`3 0 (8 * 32)) /\ (valid res.`4))].

op h__BN___negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.h__BN___negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray256.is_init _b_r 0 8) /\ (BArray256.is_init _b_a 0 (8 * 32)))) ==>
   ((BArray256.is_init res.`3 0 (8 * 32)) /\ (valid res.`4))].

op h__BN___negc1__spec _r _b_r _a _b_a _cf =
   hoare [M.h__BN___negc1_ :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray256.is_init _b_r 0 8) /\ (BArray256.is_init _b_a 0 (8 * 32)))) ==>
   ((BArray256.is_init res.`3 0 (8 * 32)) /\ (valid res.`4))].

op h__BN___neg__spec _r _b_r _a _b_a =
   hoare [M.h__BN___neg_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray256.is_init res.`3 0 (8 * 32)) /\ (valid res.`4))].

op h__BN___cminusP__spec _x _b_x _mP _b_mP _lastbit =
   hoare [M.h__BN___cminusP_ :
   (((_lastbit = lastbit) /\
    ((_b_mP = b_mP) /\ ((_mP = mP) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray256.is_init _b_mP 0 256) /\ (BArray256.is_init _b_x 0 256))) ==>
   ((BArray256.is_init res.`2 0 256) /\ (valid res.`3))].

op h__MUL__UNR____muln_innerloop_spec _x _b_x _k _istart _iend _a _b_a _b _b_b =
   hoare [M.h__MUL__UNR____muln_innerloop :
   (((_b_b = b_b) /\
    ((_b = b) /\
    ((_b_a = b_a) /\
    ((_a = a) /\
    ((_iend = iend) /\
    ((_istart = istart) /\ ((_k = k) /\ ((_b_x = b_x) /\ (_x = x))))))))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((((((0 <= _istart) /\ (_iend <= 32)) /\ (0 <= (_k - (_iend - 1)))) /\
      ((_k - _istart) < 32)) /\
     (BArray24.is_init _b_x 0 24)) /\
    (BArray256.is_init _b_a (8 * _istart) (8 * (_iend - _istart)))) /\
   (BArray256.is_init _b_b 0 (8 * 32))))))))))))) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

op h__MUL__UNR____ps_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__UNR____ps_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__UNR___ps_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__UNR___ps_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__UNR___ps_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__UNR___ps_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__UNR____sqrn_innerloop_spec _x _b_x _k _istart _iend _a _b_a =
   hoare [M.h__MUL__UNR____sqrn_innerloop :
   (((_b_a = b_a) /\
    ((_a = a) /\
    ((_iend = iend) /\
    ((_istart = istart) /\ ((_k = k) /\ ((_b_x = b_x) /\ (_x = x))))))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   ((((((0 <= _istart) /\ (_iend <= 32)) /\ (0 <= (_k - (_iend - 1)))) /\
     ((_k - _istart) < 32)) /\
    (BArray24.is_init _b_x 0 24)) /\
   (BArray256.is_init _b_a 0 (8 * 32)))))))))) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

op h__MUL__UNR____ps_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__UNR____ps_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__UNR___ps_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__UNR___ps_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__UNR___ps_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL__UNR___ps_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__UNR____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__UNR____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray512.is_init _b_a 0 (16 * 32)) /\
   (BArray512.is_init _b__P_mP 0 (16 * 32)))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__MUL__LOOP____mul1_spec _r _b_r _a _b _b_b =
   hoare [M.h__MUL__LOOP____mul1 :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray256.is_init _b_b 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (8 * (32 + 1))) /\ (valid res.`3))].

op h__MUL__LOOP____mul1acc_spec _k _r _b_r _a _b _b_b =
   hoare [M.h__MUL__LOOP____mul1acc :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= (W64.to_uint _k)) /\ ((W64.to_uint _k) < 32)) /\
    (BArray512.is_init _b_r 0 (8 * ((W64.to_uint _k) + 32)))) /\
   (BArray256.is_init _b_b 0 (8 * 32))))))) ==>
   ((true /\
    (BArray512.is_init res.`2 0 (8 * (((W64.to_uint _k) + 32) + 1)))) /\
   (valid res.`3))].

op h__MUL__LOOP___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__LOOP___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__LOOP___os_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__LOOP___os_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__LOOP___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__LOOP___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__LOOP___os_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL__LOOP___os_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__LOOP____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__LOOP____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray512.is_init _b_a 0 (16 * 32)) /\
   (BArray512.is_init _b__P_mP 0 (16 * 32)))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__MUL__XUNR____mul1_spec _r _b_r _a _b _b_b =
   hoare [M.h__MUL__XUNR____mul1 :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray256.is_init _b_b 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (8 * (32 + 1))) /\ (valid res.`3))].

op h__MUL__XUNR____mul1acc_spec _k _r _b_r _a _b _b_b =
   hoare [M.h__MUL__XUNR____mul1acc :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _k) /\ (_k < 32)) /\ (BArray512.is_init _b_r 0 (8 * (_k + 32)))) /\
   (BArray256.is_init _b_b 0 (8 * 32))))))) ==>
   ((true /\ (BArray512.is_init res.`2 0 (8 * ((_k + 32) + 1)))) /\
   (valid res.`3))].

op h__MUL__XUNR___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XUNR___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XUNR___os_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XUNR___os_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XUNR____sqr_row0_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR____sqr_row0 :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   ((2 <= 32) /\ (BArray256.is_init _b_a 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 8 (8 * 32)) /\ (valid res.`3))].

op h__MUL__XUNR____sqr_rowacc_spec _i _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR____sqr_rowacc :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_i = i))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _i) /\ (_i < (32 - 1))) /\
    (BArray512.is_init _b_r 8 (8 * ((_i + 32) - 1)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))))))) ==>
   ((true /\ (BArray512.is_init res.`2 8 (8 * (_i + 32)))) /\ (valid res.`3))].

op h__MUL__XUNR____sqr_diag_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR____sqr_diag :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (((2 <= 32) /\ (BArray512.is_init _b_r 8 (8 * ((2 * 32) - 2)))) /\
   (BArray256.is_init _b_a 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XUNR___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XUNR___os_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR___os_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XUNR____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__XUNR____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray512.is_init _b_a 0 (16 * 32)) /\
   (BArray512.is_init _b__P_mP 0 (16 * 32)))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__MUL__XLOOP____mul1_spec _r _b_r _a _b _b_b =
   hoare [M.h__MUL__XLOOP____mul1 :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray256.is_init _b_b 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (8 * (32 + 1))) /\ (valid res.`3))].

op h__MUL__XLOOP____mul1acc_spec _k _r _b_r _a _b _b_b =
   hoare [M.h__MUL__XLOOP____mul1acc :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= (W64.to_uint _k)) /\ ((W64.to_uint _k) < 32)) /\
    (BArray512.is_init _b_r 0 (8 * ((W64.to_uint _k) + 32)))) /\
   (BArray256.is_init _b_b 0 (8 * 32))))))) ==>
   ((true /\
    (BArray512.is_init res.`2 0 (8 * (((W64.to_uint _k) + 32) + 1)))) /\
   (valid res.`3))].

op h__MUL__XLOOP___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XLOOP___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XLOOP___os_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XLOOP___os_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XLOOP___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XLOOP___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XLOOP___os_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XLOOP___os_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XLOOP____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__XLOOP____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray512.is_init _b_a 0 (16 * 32)) /\
   (BArray512.is_init _b__P_mP 0 (16 * 32)))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__MUL__XREG____mulr_row0_spec _a _b _b_b =
   hoare [M.h__MUL__XREG____mulr_row0 :
   (((_b_b = b_b) /\ ((_b = b) /\ (_a = a))) /\
   (BArray256.is_init _b_b 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (8 * (32 + 1))) /\ (valid res.`3))].

op h__MUL__XREG____mulr_rowk_spec _k _t _b_t _a _b _b_b =
   hoare [M.h__MUL__XREG____mulr_rowk :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_t = b_t) /\ ((_t = t) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _k) /\ (_k < 32)) /\ (BArray512.is_init _b_t 0 (8 * (_k + 32)))) /\
   (BArray256.is_init _b_b 0 (8 * 32))))))) ==>
   ((true /\ (BArray512.is_init res.`2 0 (8 * ((_k + 32) + 1)))) /\
   (valid res.`3))].

op h__MUL__XREG___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XREG___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XREG___os_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XREG___os_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XREG____sqrr_row0_spec _a _b_a =
   hoare [M.h__MUL__XREG____sqrr_row0 :
   (((_b_a = b_a) /\ (_a = a)) /\
   ((2 <= 32) /\ (BArray256.is_init _b_a 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 8 (8 * 32)) /\ (valid res.`3))].

op h__MUL__XREG____sqrr_rowi_spec _i _t _b_t _a _b_a =
   hoare [M.h__MUL__XREG____sqrr_rowi :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_t = b_t) /\ ((_t = t) /\ (_i = i))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _i) /\ (_i < (32 - 1))) /\
    (BArray512.is_init _b_t 8 (8 * ((_i + 32) - 1)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))))))) ==>
   ((true /\ (BArray512.is_init res.`2 8 (8 * (_i + 32)))) /\ (valid res.`3))].

op h__MUL__XREG____sqrr_diag_spec _r _b_r _t _b_t _a _b_a =
   hoare [M.h__MUL__XREG____sqrr_diag :
   (((_b_a = b_a) /\
    ((_a = a) /\ ((_b_t = b_t) /\ ((_t = t) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((((2 <= 32) /\ (BArray512.is_init _b_r 8 (8 * ((2 * 32) - 10)))) /\
    (BArray512.is_init _b_t 8 (8 * ((2 * 32) - 2)))) /\
   (BArray256.is_init _b_a 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XREG___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XREG___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XREG___os_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XREG___os_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL__XREG____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__XREG____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray512.is_init _b_a 0 (16 * 32)) /\
   (BArray512.is_init _b__P_mP 0 (16 * 32)))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__MUL___muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL___muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL___sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL___sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__MUL____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray512.is_init _b_a 0 (16 * 32)) /\
   (BArray512.is_init _b__P_mP 0 (16 * 32)))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__FPM__fun_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__FPM__fun_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray256.is_init _b_a 0 (8 * 32)) /\
   (BArray256.is_init _b_b 0 (8 * 32)))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__FPM__fun_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__FPM__fun_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray256.is_init _b_a 0 (8 * 32))) ==>
   ((BArray512.is_init res.`2 0 (16 * 32)) /\ (valid res.`3))].

op h__FPM___redM_spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___redM :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray512.is_init _b_a 0 (16 * 32)) /\
   (BArray1032.is_init _b_ctx 0 (8 * 129)))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__FPM___redM__spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___redM_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray512.is_init _b_a 0 (16 * 32)) /\
   (BArray1032.is_init _b_ctx 0 (8 * 129)))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__FPM___fromM__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___fromM_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray1032.is_init _b_ctx 0 1032) /\ (BArray256.is_init _b_a 0 256))) ==>
   ((BArray256.is_init res.`2 0 256) /\ (valid res.`3))].

op h__FPM__fun_red_spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM__fun_red :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray512.is_init _b_a 0 (16 * 32)) /\
   (BArray1032.is_init _b_ctx 0 (8 * 129)))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__FPM___addm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM___addm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray256.is_init _b_a 0 (8 * 32)) /\
    (BArray256.is_init _b_b 0 (8 * 32))) /\
   (BArray1032.is_init _b_ctx (8 * 32) (8 * 32)))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__FPM___mulmU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM___mulmU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray1032.is_init _b_ctx 0 1032) /\
   ((BArray256.is_init _b_b 0 256) /\ (BArray256.is_init _b_a 0 256)))) ==>
   ((BArray256.is_init res.`2 0 256) /\ (valid res.`3))].

op h__FPM___sqrmU__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___sqrmU_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray1032.is_init _b_ctx 0 1032) /\ (BArray256.is_init _b_a 0 256))) ==>
   ((BArray256.is_init res.`2 0 256) /\ (valid res.`3))].

op h__FPM__fun_mulU_spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM__fun_mulU :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray1032.is_init _b_ctx 0 1032) /\
   ((BArray256.is_init _b_b 0 256) /\ (BArray256.is_init _b_a 0 256)))) ==>
   ((BArray256.is_init res.`2 0 256) /\ (valid res.`3))].

op h__FPM__fun_sqrU_spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM__fun_sqrU :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray1032.is_init _b_ctx 0 1032) /\ (BArray256.is_init _b_a 0 256))) ==>
   ((BArray256.is_init res.`2 0 256) /\ (valid res.`3))].

op h__FPM___toM__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___toM_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray1032.is_init _b_ctx 0 1032) /\ (BArray256.is_init _b_a 0 256))) ==>
   ((BArray256.is_init res.`2 0 256) /\ (valid res.`3))].

op h__FPM___ctx_init__spec _ctx _b_ctx _p _b_P =
   hoare [M.h__FPM___ctx_init_ :
   (((_b_P = b_P) /\ ((_p = p) /\ ((_b_ctx = b_ctx) /\ (_ctx = ctx)))) /\
   (BArray256.is_init _b_P 0 (8 * 32))) ==>
   ((BArray1032.is_init res.`2 0 (8 * 129)) /\ (valid res.`3))].

op h__FPM__EXPE___exp1mLR_first_noct_spec _r _b_r _x _b_x _w _ctx _b_ctx =
   hoare [M.h__FPM__EXPE___exp1mLR_first_noct :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_w = w) /\ ((_b_x = b_x) /\ ((_x = x) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray256.is_init _b_x 0 (8 * 32)) /\
   (BArray1032.is_init _b_ctx 0 (8 * 129)))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__FPM__EXPE___exp1mLR_noct_spec _r _b_r _x _b_x _w _ctx _b_ctx =
   hoare [M.h__FPM__EXPE___exp1mLR_noct :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_w = w) /\ ((_b_x = b_x) /\ ((_x = x) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray1032.is_init _b_ctx 0 1032) /\
   ((BArray256.is_init _b_x 0 256) /\ (BArray256.is_init _b_r 0 256)))) ==>
   ((BArray256.is_init res.`2 0 256) /\ (valid res.`3))].

op h__FPM__EXPE___expmLR_noct_spec _r _b_r _x _b_x _e _b_e _ctx _b_ctx =
   hoare [M.h__FPM__EXPE___expmLR_noct :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_e = b_e) /\
    ((_e = e) /\ ((_b_x = b_x) /\ ((_x = x) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray256.is_init _b_x 0 (8 * 32)) /\
    (BArray32.is_init _b_e 0 (8 * 4))) /\
   (BArray1032.is_init _b_ctx 0 (8 * 129)))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__FPM__EXPE___expmLR_noct__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM__EXPE___expmLR_noct_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray256.is_init _b_a 0 (8 * 32)) /\
    (BArray32.is_init _b_b 0 (8 * 4))) /\
   (BArray1032.is_init _b_ctx 0 (8 * 129)))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__RSA___ctx_init_N_spec _ctx _b_ctx _n _b_n =
   hoare [M.h__RSA___ctx_init_N :
   (((_b_n = b_n) /\ ((_n = n) /\ ((_b_ctx = b_ctx) /\ (_ctx = ctx)))) /\
   (BArray256.is_init _b_n 0 (8 * 32))) ==>
   ((BArray1032.is_init res.`2 0 (8 * 129)) /\ (valid res.`3))].

op h__RSA___ctx_init_P_spec _ctx _b_ctx _p _b_p =
   hoare [M.h__RSA___ctx_init_P :
   (((_b_p = b_p) /\ ((_p = p) /\ ((_b_ctx = b_ctx) /\ (_ctx = ctx)))) /\
   (BArray128.is_init _b_p 0 (8 * 16))) ==>
   ((BArray520.is_init res.`2 0 (8 * 65)) /\ (valid res.`3))].

op h__RSA____RSA_expand_pk_spec _pK _b_PK _pk _b_pk =
   hoare [M.h__RSA____RSA_expand_pk :
   (((_b_pk = b_pk) /\ ((_pk = pk) /\ ((_b_PK = b_PK) /\ (_pK = pK)))) /\
   (BArray288.is_init _b_pk 0 (8 * 36))) ==>
   ((BArray1064.is_init res.`2 0 (8 * (((4 * 32) + 1) + 4))) /\
   (valid res.`3))].

op h__RSA____RSA_expand_sk_spec _sK _b_SK _sk _b_sk =
   hoare [M.h__RSA____RSA_expand_sk :
   (((_b_sk = b_sk) /\ ((_sk = sk) /\ ((_b_SK = b_SK) /\ (_sK = sK)))) /\
   (BArray640.is_init _b_sk 0 (8 * 80))) ==>
   ((BArray1424.is_init res.`2 0 (8 * ((2 * ((4 * 16) + 1)) + (3 * 16)))) /\
   (valid res.`3))].

op h__RSA____RSAVP1_spec _y _b_y _s _b_s _pk _b_pk =
   hoare [M.h__RSA____RSAVP1 :
   (((_b_pk = b_pk) /\
    ((_pk = pk) /\
    ((_b_s = b_s) /\ ((_s = s) /\ ((_b_y = b_y) /\ (_y = y)))))) /\
   ((BArray256.is_init _b_s 0 (8 * 32)) /\
   (BArray1064.is_init _b_pk 0 (8 * (((4 * 32) + 1) + 4))))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op h__RSA___crt_exp_spec _r _b_r _c _b_c _dX _b_dX _ctxX _b_ctxX =
   hoare [M.h__RSA___crt_exp :
   (((_b_ctxX = b_ctxX) /\
    ((_ctxX = ctxX) /\
    ((_b_dX = b_dX) /\
    ((_dX = dX) /\
    ((_b_c = b_c) /\ ((_c = c) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray256.is_init _b_c 0 (8 * 32)) /\
    (BArray128.is_init _b_dX 0 (8 * 16))) /\
   (BArray520.is_init _b_ctxX 0 (8 * 65)))) ==>
   ((BArray128.is_init res.`2 0 (8 * 16)) /\ (valid res.`3))].

op h__RSA____RSASP1_crt_spec _s _b_s _sk _b_sk =
   hoare [M.h__RSA____RSASP1_crt :
   (((_b_sk = b_sk) /\ ((_sk = sk) /\ ((_b_s = b_s) /\ (_s = s)))) /\
   ((BArray1424.is_init _b_sk 0 1424) /\ (BArray256.is_init _b_s 0 256))) ==>
   ((BArray256.is_init res.`2 0 256) /\ (valid res.`3))].

op rsa_init_spec _pk _b_pk _sk _b_sk =
   hoare [M.rsa_init :
   (((_b_sk = b_sk) /\ ((_sk = sk) /\ ((_b_pk = b_pk) /\ (_pk = pk)))) /\
   true) ==>
   (((BArray1064.is_init res.`2 0 (8 * (((4 * 32) + 1) + 4))) /\
    (BArray1424.is_init res.`4 0 (8 * ((2 * ((4 * 16) + 1)) + (3 * 16))))) /\
   (valid res.`5))].

op rsa_dec_spec _m _b_m _c _b_c _sk _b_sk =
   hoare [M.rsa_dec :
   (((_b_sk = b_sk) /\
    ((_sk = sk) /\
    ((_b_c = b_c) /\ ((_c = c) /\ ((_b_m = b_m) /\ (_m = m)))))) /\
   ((BArray256.is_init _b_c 0 (8 * 32)) /\
   (BArray1424.is_init _b_sk 0 (8 * ((2 * ((4 * 16) + 1)) + (3 * 16)))))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].

op rsa_enc_spec _c _b_c _m _b_m _pk _b_pk =
   hoare [M.rsa_enc :
   (((_b_pk = b_pk) /\
    ((_pk = pk) /\
    ((_b_m = b_m) /\ ((_m = m) /\ ((_b_c = b_c) /\ (_c = c)))))) /\
   ((BArray256.is_init _b_m 0 (8 * 32)) /\
   (BArray1064.is_init _b_pk 0 (8 * (((4 * 32) + 1) + 4))))) ==>
   ((BArray256.is_init res.`2 0 (8 * 32)) /\ (valid res.`3))].
