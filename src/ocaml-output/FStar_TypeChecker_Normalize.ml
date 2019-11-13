open Prims
let cases :
  'Auu____10 'Auu____11 .
    ('Auu____10 -> 'Auu____11) ->
      'Auu____11 -> 'Auu____10 FStar_Pervasives_Native.option -> 'Auu____11
  =
  fun f  ->
    fun d  ->
      fun uu___0_31  ->
        match uu___0_31 with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> d
  
type closure =
  | Clos of ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option *
  closure) Prims.list * FStar_Syntax_Syntax.term *
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
  Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo *
  Prims.bool) 
  | Univ of FStar_Syntax_Syntax.universe 
  | Dummy 
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____129 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____241 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____259 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)) =
  (FStar_Pervasives_Native.None, Dummy) 
type branches =
  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
    FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list
type stack_elt =
  | Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) 
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
  
  | MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo 
  | Match of (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range)
  
  | Abs of (env * FStar_Syntax_Syntax.binders * env *
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
  FStar_Range.range) 
  | App of (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
  FStar_Range.range) 
  | Meta of (env * FStar_Syntax_Syntax.metadata * FStar_Range.range) 
  | Let of (env * FStar_Syntax_Syntax.binders *
  FStar_Syntax_Syntax.letbinding * FStar_Range.range) 
  | Cfg of FStar_TypeChecker_Cfg.cfg 
  | Debug of (FStar_Syntax_Syntax.term * FStar_Util.time) 
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____428 -> false
  
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____471 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____514 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____559 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____614 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____677 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____726 -> false
  
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____771 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____814 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____837 -> false
  
let (__proj__Debug__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.term * FStar_Util.time)) =
  fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____866 = FStar_Syntax_Util.head_and_args' t  in
    match uu____866 with | (hd1,uu____882) -> hd1
  
let mk :
  'Auu____910 .
    'Auu____910 ->
      FStar_Range.range -> 'Auu____910 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo :
  'a . FStar_TypeChecker_Cfg.cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit
  =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.FStar_TypeChecker_Cfg.memoize_lazy
        then
          let uu____953 = FStar_ST.op_Bang r  in
          match uu____953 with
          | FStar_Pervasives_Native.Some uu____979 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____1034 =
      FStar_List.map
        (fun uu____1050  ->
           match uu____1050 with
           | (bopt,c) ->
               let uu____1064 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____1069 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____1064 uu____1069) env
       in
    FStar_All.pipe_right uu____1034 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___1_1077  ->
    match uu___1_1077 with
    | Clos (env,t,uu____1081,uu____1082) ->
        let uu____1129 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____1139 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____1129 uu____1139
    | Univ uu____1142 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___2_1151  ->
    match uu___2_1151 with
    | Arg (c,uu____1154,uu____1155) ->
        let uu____1156 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1156
    | MemoLazy uu____1159 -> "MemoLazy"
    | Abs (uu____1167,bs,uu____1169,uu____1170,uu____1171) ->
        let uu____1176 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1176
    | UnivArgs uu____1187 -> "UnivArgs"
    | Match uu____1195 -> "Match"
    | App (uu____1205,t,uu____1207,uu____1208) ->
        let uu____1209 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____1209
    | Meta (uu____1212,m,uu____1214) -> "Meta"
    | Let uu____1216 -> "Let"
    | Cfg uu____1226 -> "Cfg"
    | Debug (t,uu____1229) ->
        let uu____1230 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____1230
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____1244 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____1244 (FStar_String.concat "; ")
  
let is_empty : 'Auu____1259 . 'Auu____1259 Prims.list -> Prims.bool =
  fun uu___3_1267  ->
    match uu___3_1267 with | [] -> true | uu____1271 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___114_1304  ->
           match () with
           | () ->
               let uu____1305 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1305) ()
      with
      | uu___113_1322 ->
          let uu____1323 =
            let uu____1325 = FStar_Syntax_Print.db_to_string x  in
            let uu____1327 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1325
              uu____1327
             in
          failwith uu____1323
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____1338 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____1338
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____1345 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____1345
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____1352 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____1352
          then
            FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
          else FStar_Pervasives_Native.None))
  
let (norm_universe :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____1390 =
            FStar_List.fold_left
              (fun uu____1416  ->
                 fun u1  ->
                   match uu____1416 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1441 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1441 with
                        | (k_u,n1) ->
                            let uu____1459 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1459
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1390 with
          | (uu____1480,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___148_1506  ->
                    match () with
                    | () ->
                        let uu____1509 =
                          let uu____1510 = FStar_List.nth env x  in
                          FStar_Pervasives_Native.snd uu____1510  in
                        (match uu____1509 with
                         | Univ u3 ->
                             ((let uu____1529 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____1529
                               then
                                 let uu____1534 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu____1534
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____1539 ->
                             let uu____1540 =
                               let uu____1542 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____1542
                                in
                             failwith uu____1540)) ()
               with
               | uu____1552 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____1558 =
                        let uu____1560 = FStar_Util.string_of_int x  in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____1560
                         in
                      failwith uu____1558))
          | FStar_Syntax_Syntax.U_unif uu____1565 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1574 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1583 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1590 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1590 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____1607 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1607 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1618 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1628 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1628 with
                                  | (uu____1635,m) -> n1 <= m))
                           in
                        if uu____1618 then rest1 else us1
                    | uu____1644 -> us1)
               | uu____1650 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1654 = aux u3  in
              FStar_List.map (fun _1657  -> FStar_Syntax_Syntax.U_succ _1657)
                uu____1654
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1661 = aux u  in
           match uu____1661 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
  
let rec (inline_closure_env :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____1830  ->
               let uu____1831 = FStar_Syntax_Print.tag_of_term t  in
               let uu____1833 = env_to_string env  in
               let uu____1835 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____1831 uu____1833 uu____1835);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____1848 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1851 ->
                    let uu____1874 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____1874
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____1875 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____1876 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____1877 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____1878 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____1903 ->
                           let uu____1916 =
                             let uu____1918 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____1920 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____1918 uu____1920
                              in
                           failwith uu____1916
                       | uu____1925 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___4_1961  ->
                                         match uu___4_1961 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____1968 =
                                               let uu____1975 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____1975)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____1968
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___242_1987 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___242_1987.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___242_1987.FStar_Syntax_Syntax.sort)
                                                  })
                                                in
                                             let t1 =
                                               inline_closure_env cfg env []
                                                 x_i
                                                in
                                             (match t1.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_bvar
                                                  x_j ->
                                                  FStar_Syntax_Syntax.NM
                                                    (x,
                                                      (x_j.FStar_Syntax_Syntax.index))
                                              | uu____1993 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____1996 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___251_2001 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___251_2001.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___251_2001.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____2022 =
                        let uu____2023 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____2023  in
                      mk uu____2022 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____2031 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2031  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____2033 = lookup_bvar env x  in
                    (match uu____2033 with
                     | Univ uu____2036 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___267_2041 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___267_2041.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___267_2041.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____2047,uu____2048) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____2139  ->
                              fun stack1  ->
                                match uu____2139 with
                                | (a,aq) ->
                                    let uu____2151 =
                                      let uu____2152 =
                                        let uu____2159 =
                                          let uu____2160 =
                                            let uu____2192 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____2192, false)  in
                                          Clos uu____2160  in
                                        (uu____2159, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____2152  in
                                    uu____2151 :: stack1) args)
                       in
                    inline_closure_env cfg env stack1 head1
                | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                    let env' =
                      FStar_All.pipe_right env
                        (FStar_List.fold_right
                           (fun _b  ->
                              fun env1  ->
                                (FStar_Pervasives_Native.None, Dummy) :: env1)
                           bs)
                       in
                    let stack1 =
                      (Abs (env, bs, env', lopt, (t.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env' stack1 body
                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                    let uu____2360 = close_binders cfg env bs  in
                    (match uu____2360 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____2410) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env stack
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____2421 =
                      let uu____2434 =
                        let uu____2443 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____2443]  in
                      close_binders cfg env uu____2434  in
                    (match uu____2421 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____2488 =
                             let uu____2489 =
                               let uu____2496 =
                                 let uu____2497 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____2497
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____2496, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____2489  in
                           mk uu____2488 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2596 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____2596
                      | FStar_Util.Inr c ->
                          let uu____2610 = close_comp cfg env c  in
                          FStar_Util.Inr uu____2610
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____2629 =
                        let uu____2630 =
                          let uu____2657 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____2657, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2630  in
                      mk uu____2629 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____2703 =
                            let uu____2704 =
                              let uu____2711 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____2711, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____2704  in
                          mk uu____2703 t.FStar_Syntax_Syntax.pos
                      | FStar_Syntax_Syntax.Quote_static  ->
                          let qi1 =
                            FStar_Syntax_Syntax.on_antiquoted
                              (non_tail_inline_closure_env cfg env) qi
                             in
                          mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                            t.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                    let stack1 = (Meta (env, m, (t.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env stack1 t'
                | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                    let env0 = env  in
                    let env1 =
                      FStar_List.fold_left
                        (fun env1  -> fun uu____2766  -> dummy :: env1) env
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    let typ =
                      non_tail_inline_closure_env cfg env1
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let def =
                      non_tail_inline_closure_env cfg env1
                        lb.FStar_Syntax_Syntax.lbdef
                       in
                    let uu____2787 =
                      let uu____2798 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____2798
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____2820 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___359_2836 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___359_2836.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___359_2836.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2820))
                       in
                    (match uu____2787 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___364_2854 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___364_2854.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___364_2854.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___364_2854.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___364_2854.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2871,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____2937  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____2954 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2954
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____2969  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____2993 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2993
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___387_3004 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___387_3004.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___387_3004.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___390_3005 = lb  in
                      let uu____3006 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___390_3005.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___390_3005.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____3006;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___390_3005.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___390_3005.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____3038  -> fun env1  -> dummy :: env1)
                          lbs1 env
                         in
                      non_tail_inline_closure_env cfg body_env body  in
                    let t1 =
                      mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                        t.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                    let stack1 =
                      (Match
                         (env, branches, cfg, (t.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env stack1 head1))

and (non_tail_inline_closure_env :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun cfg  -> fun env  -> fun t  -> inline_closure_env cfg env [] t

and (rebuild_closure :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____3130  ->
               let uu____3131 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3133 = env_to_string env  in
               let uu____3135 = stack_to_string stack  in
               let uu____3137 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____3131 uu____3133 uu____3135 uu____3137);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____3144,uu____3145),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____3226 = close_binders cfg env' bs  in
               (match uu____3226 with
                | (bs1,uu____3242) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____3262 =
                      let uu___448_3265 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___448_3265.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___448_3265.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____3262)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____3321 =
                 match uu____3321 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3436 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____3467 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3556  ->
                                     fun uu____3557  ->
                                       match (uu____3556, uu____3557) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____3707 = norm_pat env4 p1
                                              in
                                           (match uu____3707 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____3467 with
                            | (pats1,env4) ->
                                ((let uu___485_3877 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___485_3877.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___489_3898 = x  in
                             let uu____3899 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___489_3898.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___489_3898.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3899
                             }  in
                           ((let uu___492_3913 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___492_3913.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___496_3924 = x  in
                             let uu____3925 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___496_3924.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___496_3924.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3925
                             }  in
                           ((let uu___499_3939 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___499_3939.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___505_3955 = x  in
                             let uu____3956 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___505_3955.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___505_3955.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3956
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___509_3973 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___509_3973.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____3978 = norm_pat env2 pat  in
                     (match uu____3978 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____4047 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____4047
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____4066 =
                   let uu____4067 =
                     let uu____4090 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____4090)  in
                   FStar_Syntax_Syntax.Tm_match uu____4067  in
                 mk uu____4066 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
                     let uu____4226 =
                       let uu____4247 =
                         FStar_All.pipe_right names1
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m))
                          in
                       let uu____4264 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1  ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu____4373  ->
                                         match uu____4373 with
                                         | (a,q) ->
                                             let uu____4400 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a
                                                in
                                             (uu____4400, q)))))
                          in
                       (uu____4247, uu____4264)  in
                     FStar_Syntax_Syntax.Meta_pattern uu____4226
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4429 =
                       let uu____4436 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4436)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4429
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4448 =
                       let uu____4457 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4457)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4448
                 | uu____4462 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____4468 -> failwith "Impossible: unexpected stack element")

and (close_imp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun imp  ->
        match imp with
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
            let uu____4484 =
              let uu____4485 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____4485  in
            FStar_Pervasives_Native.Some uu____4484
        | i -> i

and (close_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) Prims.list * env))
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____4502 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4586  ->
                  fun uu____4587  ->
                    match (uu____4586, uu____4587) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___564_4727 = b  in
                          let uu____4728 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___564_4727.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___564_4727.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4728
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____4502 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

and (close_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
            -> c
        | uu____4870 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4883 = inline_closure_env cfg env [] t  in
                 let uu____4884 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4883 uu____4884
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4897 = inline_closure_env cfg env [] t  in
                 let uu____4898 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4897 uu____4898
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____4952  ->
                           match uu____4952 with
                           | (a,q) ->
                               let uu____4973 =
                                 inline_closure_env cfg env [] a  in
                               (uu____4973, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_4990  ->
                           match uu___5_4990 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4994 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____4994
                           | f -> f))
                    in
                 let uu____4998 =
                   let uu___597_4999 = c1  in
                   let uu____5000 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5000;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___597_4999.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____4998)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___6_5010  ->
            match uu___6_5010 with
            | FStar_Syntax_Syntax.DECREASES uu____5012 -> false
            | uu____5016 -> true))

and (close_lcomp_opt :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___7_5035  ->
                      match uu___7_5035 with
                      | FStar_Syntax_Syntax.DECREASES uu____5037 -> false
                      | uu____5041 -> true))
               in
            let rc1 =
              let uu___614_5044 = rc  in
              let uu____5045 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___614_5044.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5045;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5054 -> lopt

let (closure_as_term :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun cfg  -> fun env  -> fun t  -> non_tail_inline_closure_env cfg env t 
let (unembed_binder_knot :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____5102 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____5102 with
    | FStar_Pervasives_Native.Some e ->
        let uu____5141 = FStar_Syntax_Embeddings.unembed e t  in
        uu____5141 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____5161 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'Auu____5161) FStar_Pervasives_Native.option
        * closure) Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____5223  ->
           fun subst1  ->
             match uu____5223 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____5264,uu____5265)) ->
                      let uu____5326 = b  in
                      (match uu____5326 with
                       | (bv,uu____5334) ->
                           let uu____5335 =
                             let uu____5337 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5337  in
                           if uu____5335
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____5345 = unembed_binder term1  in
                              match uu____5345 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5352 =
                                      let uu___649_5353 = bv  in
                                      let uu____5354 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___649_5353.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___649_5353.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5354
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5352
                                     in
                                  let b_for_x =
                                    let uu____5360 =
                                      let uu____5367 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5367)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5360  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___8_5383  ->
                                         match uu___8_5383 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5385,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5387;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5388;_})
                                             ->
                                             let uu____5393 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5393
                                         | uu____5395 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____5397 -> subst1)) env []
  
let reduce_primops :
  'Auu____5419 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____5419)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun env  ->
        fun tm  ->
          if
            Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
          then tm
          else
            (let uu____5471 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5471 with
             | (head1,args) ->
                 let uu____5516 =
                   let uu____5517 = FStar_Syntax_Util.un_uinst head1  in
                   uu____5517.FStar_Syntax_Syntax.n  in
                 (match uu____5516 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5523 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5523 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok
                             ||
                             (Prims.op_Negation
                                cfg.FStar_TypeChecker_Cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.FStar_TypeChecker_Cfg.arity
                           then
                             (FStar_TypeChecker_Cfg.log_primops cfg
                                (fun uu____5546  ->
                                   let uu____5547 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5549 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5551 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5547 uu____5549 uu____5551);
                              tm)
                           else
                             (let uu____5556 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5556 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5642  ->
                                        let uu____5643 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5643);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5648  ->
                                             if
                                               prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let r =
                                      prim_step.FStar_TypeChecker_Cfg.interpretation
                                        psc norm_cb args_1
                                       in
                                    match r with
                                    | FStar_Pervasives_Native.None  ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5662  ->
                                              let uu____5663 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5663);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5671  ->
                                              let uu____5672 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5674 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5672 uu____5674);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5677 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5681  ->
                                 let uu____5682 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5682);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5688  ->
                            let uu____5689 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5689);
                       (match args with
                        | (a1,uu____5695)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5720 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5734  ->
                            let uu____5735 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5735);
                       (match args with
                        | (t,uu____5741)::(r,uu____5743)::[] ->
                            let uu____5784 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5784 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5790 -> tm))
                  | uu____5801 -> tm))
  
let reduce_equality :
  'Auu____5812 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____5812)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___737_5861 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___739_5864 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___739_5864.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___739_5864.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___739_5864.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___739_5864.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___739_5864.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___739_5864.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___739_5864.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___739_5864.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___739_5864.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___739_5864.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___739_5864.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___739_5864.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___739_5864.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___739_5864.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___739_5864.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___739_5864.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___739_5864.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___739_5864.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___737_5861.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___737_5861.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___737_5861.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___737_5861.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___737_5861.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___737_5861.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___737_5861.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____5875 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____5886 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____5897 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd1  ->
    fun args  ->
      let aux min_args =
        let uu____5918 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____5918
          (fun n1  ->
             if n1 < min_args
             then Norm_request_none
             else
               if n1 = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____5950 =
        let uu____5951 = FStar_Syntax_Util.un_uinst hd1  in
        uu____5951.FStar_Syntax_Syntax.n  in
      match uu____5950 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.of_int (2))
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux Prims.int_one
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.of_int (3))
      | uu____5960 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____5969 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____5969)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd1  ->
    fun args  ->
      let uu____5982 =
        let uu____5983 = FStar_Syntax_Util.un_uinst hd1  in
        uu____5983.FStar_Syntax_Syntax.n  in
      match uu____5982 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6041 = FStar_Syntax_Util.mk_app hd1 [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____6041 rest
           | uu____6068 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6108 = FStar_Syntax_Util.mk_app hd1 [t]  in
               FStar_Syntax_Util.mk_app uu____6108 rest
           | uu____6127 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when (FStar_List.length rest) > Prims.int_zero
               ->
               let uu____6201 = FStar_Syntax_Util.mk_app hd1 [t1; t2; t3]  in
               FStar_Syntax_Util.mk_app uu____6201 rest
           | uu____6236 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____6238 ->
          let uu____6239 =
            let uu____6241 = FStar_Syntax_Print.term_to_string hd1  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____6241
             in
          failwith uu____6239
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_6262  ->
    match uu___9_6262 with
    | FStar_Syntax_Embeddings.Zeta  -> [FStar_TypeChecker_Env.Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [FStar_TypeChecker_Env.Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [FStar_TypeChecker_Env.Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [FStar_TypeChecker_Env.Weak]
    | FStar_Syntax_Embeddings.HNF  -> [FStar_TypeChecker_Env.HNF]
    | FStar_Syntax_Embeddings.Primops  -> [FStar_TypeChecker_Env.Primops]
    | FStar_Syntax_Embeddings.Reify  -> [FStar_TypeChecker_Env.Reify]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____6269 =
          let uu____6272 =
            let uu____6273 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldOnly uu____6273  in
          [uu____6272]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6269
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____6281 =
          let uu____6284 =
            let uu____6285 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldFully uu____6285  in
          [uu____6284]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6281
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____6293 =
          let uu____6296 =
            let uu____6297 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldAttr uu____6297  in
          [uu____6296]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6293
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____6322 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'Auu____6322) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____6373 =
            let uu____6378 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6378 s  in
          match uu____6373 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6394 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____6394
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
             then [FStar_TypeChecker_Env.EraseUniverses]
             else [])
            (FStar_List.append
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                then [FStar_TypeChecker_Env.AllowUnboundUniverses]
                else [])
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.nbe_step
                then [FStar_TypeChecker_Env.NBE]
                else []))
           in
        match args with
        | uu____6429::(tm,uu____6431)::[] ->
            let s =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.Iota;
              FStar_TypeChecker_Env.Primops;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____6460)::[] ->
            let s =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.Iota;
              FStar_TypeChecker_Env.Primops;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____6481)::uu____6482::(tm,uu____6484)::[] ->
            let add_exclude s z =
              let uu____6522 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____6522
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____6529 =
              let uu____6534 = full_norm steps  in parse_steps uu____6534  in
            (match uu____6529 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____6573 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6605 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6612  ->
                    match uu___10_6612 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6614 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6616 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6620 -> true
                    | uu____6624 -> false))
             in
          if uu____6605
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6634  ->
             let uu____6635 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6635);
        (let tm_norm =
           let uu____6639 =
             let uu____6654 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6654.FStar_TypeChecker_Env.nbe  in
           uu____6639 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6658  ->
              let uu____6659 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6659);
         tm_norm)
  
let firstn :
  'Auu____6669 .
    Prims.int ->
      'Auu____6669 Prims.list ->
        ('Auu____6669 Prims.list * 'Auu____6669 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___11_6726 =
        match uu___11_6726 with
        | (MemoLazy uu____6731)::s -> drop_irrel s
        | (UnivArgs uu____6741)::s -> drop_irrel s
        | s -> s  in
      let uu____6754 = drop_irrel stack  in
      match uu____6754 with
      | (App
          (uu____6758,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6759;
                        FStar_Syntax_Syntax.vars = uu____6760;_},uu____6761,uu____6762))::uu____6763
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6768 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6797) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6807) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6828  ->
                  match uu____6828 with
                  | (a,uu____6839) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6850 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6875 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6877 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6891 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6893 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6895 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6897 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6899 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6902 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6910 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6918 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6933 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6953 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6969 -> true
    | FStar_Syntax_Syntax.Tm_match uu____6977 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7049  ->
                   match uu____7049 with
                   | (a,uu____7060) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____7071) ->
        ((maybe_weakly_reduced t1) ||
           (match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> maybe_weakly_reduced t2
            | FStar_Util.Inr c2 -> aux_comp c2))
          ||
          ((match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> false
            | FStar_Pervasives_Native.Some tac -> maybe_weakly_reduced tac))
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        (maybe_weakly_reduced t1) ||
          ((match m with
            | FStar_Syntax_Syntax.Meta_pattern (uu____7170,args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7225  ->
                        match uu____7225 with
                        | (a,uu____7236) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7245,uu____7246,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7252,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____7258 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____7268 -> false
            | FStar_Syntax_Syntax.Meta_named uu____7270 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____7281 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____7292 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____7303 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____7314 -> false
  
let (should_unfold :
  FStar_TypeChecker_Cfg.cfg ->
    (FStar_TypeChecker_Cfg.cfg -> Prims.bool) ->
      FStar_Syntax_Syntax.fv ->
        FStar_TypeChecker_Env.qninfo -> should_unfold_res)
  =
  fun cfg  ->
    fun should_reify1  ->
      fun fv  ->
        fun qninfo  ->
          let attrs =
            let uu____7347 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____7347 with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some ats -> ats  in
          let yes = (true, false, false)  in
          let no = (false, false, false)  in
          let fully = (true, true, false)  in
          let reif = (true, false, true)  in
          let yesno b = if b then yes else no  in
          let fullyno b = if b then fully else no  in
          let comb_or l =
            FStar_List.fold_right
              (fun uu____7546  ->
                 fun uu____7547  ->
                   match (uu____7546, uu____7547) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____7653 =
            match uu____7653 with
            | (x,y,z) ->
                let uu____7673 = FStar_Util.string_of_bool x  in
                let uu____7675 = FStar_Util.string_of_bool y  in
                let uu____7677 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____7673 uu____7675
                  uu____7677
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7705  ->
                    let uu____7706 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____7708 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7706 uu____7708);
               if b then reif else no)
            else
              if
                (let uu____7723 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____7723)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7728  ->
                      FStar_Util.print_string
                        " >> It's a primop, not unfolding\n");
                 no)
              else
                (match (qninfo,
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only),
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully),
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr))
                 with
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7763),uu____7764);
                        FStar_Syntax_Syntax.sigrng = uu____7765;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7767;
                        FStar_Syntax_Syntax.sigattrs = uu____7768;_},uu____7769),uu____7770),uu____7771,uu____7772,uu____7773)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7880  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7882,uu____7883,uu____7884,uu____7885) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7952  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7955),uu____7956);
                        FStar_Syntax_Syntax.sigrng = uu____7957;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7959;
                        FStar_Syntax_Syntax.sigattrs = uu____7960;_},uu____7961),uu____7962),uu____7963,uu____7964,uu____7965)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8072  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8074,FStar_Pervasives_Native.Some
                    uu____8075,uu____8076,uu____8077) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8145  ->
                           let uu____8146 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8146);
                      (let uu____8149 =
                         let uu____8161 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8187 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8187
                            in
                         let uu____8199 =
                           let uu____8211 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8237 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8237
                              in
                           let uu____8253 =
                             let uu____8265 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8291 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8291
                                in
                             [uu____8265]  in
                           uu____8211 :: uu____8253  in
                         uu____8161 :: uu____8199  in
                       comb_or uu____8149))
                 | (uu____8339,uu____8340,FStar_Pervasives_Native.Some
                    uu____8341,uu____8342) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8410  ->
                           let uu____8411 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8411);
                      (let uu____8414 =
                         let uu____8426 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8452 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8452
                            in
                         let uu____8464 =
                           let uu____8476 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8502 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8502
                              in
                           let uu____8518 =
                             let uu____8530 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8556 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8556
                                in
                             [uu____8530]  in
                           uu____8476 :: uu____8518  in
                         uu____8426 :: uu____8464  in
                       comb_or uu____8414))
                 | (uu____8604,uu____8605,uu____8606,FStar_Pervasives_Native.Some
                    uu____8607) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8675  ->
                           let uu____8676 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8676);
                      (let uu____8679 =
                         let uu____8691 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8717 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8717
                            in
                         let uu____8729 =
                           let uu____8741 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8767 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8767
                              in
                           let uu____8783 =
                             let uu____8795 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8821 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8821
                                in
                             [uu____8795]  in
                           uu____8741 :: uu____8783  in
                         uu____8691 :: uu____8729  in
                       comb_or uu____8679))
                 | uu____8869 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8915  ->
                           let uu____8916 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____8918 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____8920 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____8916 uu____8918 uu____8920);
                      (let uu____8923 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_8929  ->
                                 match uu___12_8929 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____8935 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____8935 l))
                          in
                       FStar_All.pipe_left yesno uu____8923)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____8951  ->
               let uu____8952 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____8954 =
                 let uu____8956 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____8956  in
               let uu____8957 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____8952 uu____8954 uu____8957);
          (match res with
           | (false ,uu____8960,uu____8961) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____8986 ->
               let uu____8996 =
                 let uu____8998 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____8998
                  in
               FStar_All.pipe_left failwith uu____8996)
  
let decide_unfolding :
  'Auu____9017 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____9017 ->
            FStar_Syntax_Syntax.fv ->
              FStar_TypeChecker_Env.qninfo ->
                (FStar_TypeChecker_Cfg.cfg * stack_elt Prims.list)
                  FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun rng  ->
          fun fv  ->
            fun qninfo  ->
              let res =
                should_unfold cfg (fun cfg1  -> should_reify cfg1 stack) fv
                  qninfo
                 in
              match res with
              | Should_unfold_no  -> FStar_Pervasives_Native.None
              | Should_unfold_yes  ->
                  FStar_Pervasives_Native.Some (cfg, stack)
              | Should_unfold_fully  ->
                  let cfg' =
                    let uu___1144_9086 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1146_9089 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.delta_constant);
                           FStar_TypeChecker_Cfg.unfold_only =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Cfg.unfold_fully =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Cfg.unfold_attr =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  let stack' =
                    match stack with
                    | (UnivArgs (us,r))::stack' -> (UnivArgs (us, r)) ::
                        (Cfg cfg) :: stack'
                    | stack' -> (Cfg cfg) :: stack'  in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify  ->
                  let rec push1 e s =
                    match s with
                    | [] -> [e]
                    | (UnivArgs (us,r))::t ->
                        let uu____9151 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____9151
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____9163 =
                      let uu____9170 =
                        let uu____9171 =
                          let uu____9172 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____9172  in
                        FStar_Syntax_Syntax.Tm_constant uu____9171  in
                      FStar_Syntax_Syntax.mk uu____9170  in
                    uu____9163 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let stack1 =
                    push1
                      (App
                         (env, ref, FStar_Pervasives_Native.None,
                           FStar_Range.dummyRange)) stack
                     in
                  FStar_Pervasives_Native.Some (cfg, stack1)
  
let (on_domain_lids : FStar_Ident.lident Prims.list) =
  let fext_lid s =
    FStar_Ident.lid_of_path ["FStar"; "FunctionalExtensionality"; s]
      FStar_Range.dummyRange
     in
  FStar_All.pipe_right ["on_domain"; "on_dom"; "on_domain_g"; "on_dom_g"]
    (FStar_List.map fext_lid)
  
let (is_fext_on_domain :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let is_on_dom fv =
      FStar_All.pipe_right on_domain_lids
        (FStar_List.existsb (fun l  -> FStar_Syntax_Syntax.fv_eq_lid fv l))
       in
    let uu____9238 =
      let uu____9239 = FStar_Syntax_Subst.compress t  in
      uu____9239.FStar_Syntax_Syntax.n  in
    match uu____9238 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9270 =
          let uu____9271 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9271.FStar_Syntax_Syntax.n  in
        (match uu____9270 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____9288 =
                 let uu____9295 =
                   let uu____9306 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____9306 FStar_List.tl  in
                 FStar_All.pipe_right uu____9295 FStar_List.hd  in
               FStar_All.pipe_right uu____9288 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____9405 -> FStar_Pervasives_Native.None)
    | uu____9406 -> FStar_Pervasives_Native.None
  
let rec (norm :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            if
              (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.norm_delayed
            then
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____9685 ->
                   let uu____9708 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9708
               | uu____9711 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9721  ->
               let uu____9722 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9724 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9726 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9728 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9736 =
                 let uu____9738 =
                   let uu____9741 = firstn (Prims.of_int (4)) stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9741
                    in
                 stack_to_string uu____9738  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9722 uu____9724 uu____9726 uu____9728 uu____9736);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9769  ->
               let uu____9770 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9770);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9776  ->
                     let uu____9777 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9777);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9780 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9784  ->
                     let uu____9785 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9785);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____9788 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9792  ->
                     let uu____9793 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9793);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9796 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9800  ->
                     let uu____9801 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9801);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9804;
                 FStar_Syntax_Syntax.fv_delta = uu____9805;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9809  ->
                     let uu____9810 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9810);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9813;
                 FStar_Syntax_Syntax.fv_delta = uu____9814;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9815);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9825  ->
                     let uu____9826 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9826);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____9832 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____9832 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _9835) when
                    _9835 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____9839  ->
                          let uu____9840 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9840);
                     rebuild cfg env stack t1)
                | uu____9843 ->
                    let uu____9846 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____9846 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
               let qi1 =
                 FStar_Syntax_Syntax.on_antiquoted (norm cfg env []) qi  in
               let t2 =
                 mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                   t1.FStar_Syntax_Syntax.pos
                  in
               let uu____9885 = closure_as_term cfg env t2  in
               rebuild cfg env stack uu____9885
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9913 = is_norm_request hd1 args  in
                  uu____9913 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____9919 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____9919))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9947 = is_norm_request hd1 args  in
                  uu____9947 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1257_9954 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1259_9957 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1259_9957.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1257_9954.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1257_9954.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1257_9954.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1257_9954.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1257_9954.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1257_9954.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____9964 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____9964 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____10000  ->
                                 fun stack1  ->
                                   match uu____10000 with
                                   | (a,aq) ->
                                       let uu____10012 =
                                         let uu____10013 =
                                           let uu____10020 =
                                             let uu____10021 =
                                               let uu____10053 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____10053, false)
                                                in
                                             Clos uu____10021  in
                                           (uu____10020, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____10013  in
                                       uu____10012 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10121  ->
                            let uu____10122 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10122);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____10149 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____10149)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____10160 =
                            let uu____10162 =
                              let uu____10164 =
                                FStar_Util.time_diff start fin  in
                              FStar_Pervasives_Native.snd uu____10164  in
                            FStar_Util.string_of_int uu____10162  in
                          let uu____10171 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____10173 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____10160 uu____10171 uu____10173)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____10192 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____10192)
                      else ();
                      (let delta_level =
                         let uu____10200 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___13_10207  ->
                                   match uu___13_10207 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____10209 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____10211 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____10215 -> true
                                   | uu____10219 -> false))
                            in
                         if uu____10200
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___1300_10227 = cfg  in
                         let uu____10228 =
                           let uu___1302_10229 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1302_10229.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____10228;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___1300_10227.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___1300_10227.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___1300_10227.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___1300_10227.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___1300_10227.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___1300_10227.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____10237 =
                             let uu____10238 =
                               let uu____10243 = FStar_Util.now ()  in
                               (t1, uu____10243)  in
                             Debug uu____10238  in
                           uu____10237 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10248 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10248
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10259 =
                      let uu____10266 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10266, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10259  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10275 = lookup_bvar env x  in
               (match uu____10275 with
                | Univ uu____10276 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____10330 = FStar_ST.op_Bang r  in
                      (match uu____10330 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10426  ->
                                 let uu____10427 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10429 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10427
                                   uu____10429);
                            (let uu____10432 = maybe_weakly_reduced t'  in
                             if uu____10432
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____10435 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10479)::uu____10480 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10491,uu____10492))::stack_rest ->
                    (match c with
                     | Univ uu____10496 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10505 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10535  ->
                                    let uu____10536 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10536);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10572  ->
                                    let uu____10573 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10573);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10621  ->
                          let uu____10622 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10622);
                     norm cfg env stack1 t1)
                | (Match uu____10625)::uu____10626 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10641 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10641 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10677  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____10721 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10721)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1420_10729 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1420_10729.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1420_10729.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10730 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10736  ->
                                 let uu____10737 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10737);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1427_10752 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1427_10752.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1427_10752.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1427_10752.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1427_10752.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1427_10752.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1427_10752.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1427_10752.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1427_10752.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____10756)::uu____10757 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10768 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10768 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10804  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____10848 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10848)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1420_10856 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1420_10856.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1420_10856.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10857 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10863  ->
                                 let uu____10864 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10864);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1427_10879 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1427_10879.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1427_10879.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1427_10879.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1427_10879.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1427_10879.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1427_10879.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1427_10879.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1427_10879.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10883)::uu____10884 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10897 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10897 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10933  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____10977 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10977)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1420_10985 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1420_10985.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1420_10985.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10986 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10992  ->
                                 let uu____10993 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10993);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1427_11008 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1427_11008.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1427_11008.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1427_11008.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1427_11008.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1427_11008.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1427_11008.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1427_11008.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1427_11008.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11012)::uu____11013 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11028 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11028 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11064  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11108 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11108)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1420_11116 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1420_11116.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1420_11116.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11117 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11123  ->
                                 let uu____11124 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11124);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1427_11139 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1427_11139.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1427_11139.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1427_11139.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1427_11139.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1427_11139.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1427_11139.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1427_11139.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1427_11139.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11143)::uu____11144 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11159 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11159 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11195  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11239 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11239)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1420_11247 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1420_11247.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1420_11247.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11248 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11254  ->
                                 let uu____11255 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11255);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1427_11270 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1427_11270.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1427_11270.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1427_11270.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1427_11270.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1427_11270.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1427_11270.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1427_11270.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1427_11270.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11274)::uu____11275 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11294 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11294 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11330  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11374 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11374)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1420_11382 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1420_11382.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1420_11382.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11383 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11389  ->
                                 let uu____11390 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11390);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1427_11405 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1427_11405.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1427_11405.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1427_11405.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1427_11405.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1427_11405.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1427_11405.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1427_11405.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1427_11405.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11413 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11413 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11449  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11493 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11493)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1420_11501 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1420_11501.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1420_11501.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11502 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11508  ->
                                 let uu____11509 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11509);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1427_11524 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1427_11524.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1427_11524.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1427_11524.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1427_11524.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1427_11524.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1427_11524.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1427_11524.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1427_11524.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let strict_args =
                 let uu____11560 =
                   let uu____11561 = FStar_Syntax_Util.un_uinst head1  in
                   uu____11561.FStar_Syntax_Syntax.n  in
                 match uu____11560 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11570 -> FStar_Pervasives_Native.None  in
               (match strict_args with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11591  ->
                              fun stack1  ->
                                match uu____11591 with
                                | (a,aq) ->
                                    let uu____11603 =
                                      let uu____11604 =
                                        let uu____11611 =
                                          let uu____11612 =
                                            let uu____11644 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____11644, false)  in
                                          Clos uu____11612  in
                                        (uu____11611, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11604  in
                                    uu____11603 :: stack1) args)
                       in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11712  ->
                          let uu____11713 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____11713);
                     norm cfg env stack1 head1)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____11764  ->
                              match uu____11764 with
                              | (a,i) ->
                                  let uu____11775 = norm cfg env [] a  in
                                  (uu____11775, i)))
                       in
                    let norm_args_len = FStar_List.length norm_args  in
                    let uu____11781 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i  ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____11796 = FStar_List.nth norm_args i
                                    in
                                 match uu____11796 with
                                 | (arg_i,uu____11807) ->
                                     let uu____11808 =
                                       FStar_Syntax_Util.head_and_args arg_i
                                        in
                                     (match uu____11808 with
                                      | (head2,uu____11827) ->
                                          let uu____11852 =
                                            let uu____11853 =
                                              FStar_Syntax_Util.un_uinst
                                                head2
                                               in
                                            uu____11853.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____11852 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____11857 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____11860 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv
                                                  in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____11860
                                           | uu____11861 -> false)))))
                       in
                    if uu____11781
                    then
                      let stack1 =
                        FStar_All.pipe_right stack
                          (FStar_List.fold_right
                             (fun uu____11878  ->
                                fun stack1  ->
                                  match uu____11878 with
                                  | (a,aq) ->
                                      let uu____11890 =
                                        let uu____11891 =
                                          let uu____11898 =
                                            let uu____11899 =
                                              let uu____11931 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a))
                                                 in
                                              (env, a, uu____11931, false)
                                               in
                                            Clos uu____11899  in
                                          (uu____11898, aq,
                                            (t1.FStar_Syntax_Syntax.pos))
                                           in
                                        Arg uu____11891  in
                                      uu____11890 :: stack1) norm_args)
                         in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12013  ->
                            let uu____12014 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12014);
                       norm cfg env stack1 head1)
                    else
                      (let head2 = closure_as_term cfg env head1  in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head2 norm_args
                           FStar_Pervasives_Native.None
                           t1.FStar_Syntax_Syntax.pos
                          in
                       rebuild cfg env stack term))
           | FStar_Syntax_Syntax.Tm_refine (x,uu____12034) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
               -> norm cfg env stack x.FStar_Syntax_Syntax.sort
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 (match (env, stack) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort
                         in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___1489_12079 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1489_12079.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1489_12079.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12080 ->
                      let uu____12095 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12095)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12099 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12099 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12130 =
                          let uu____12131 =
                            let uu____12138 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1498_12144 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1498_12144.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1498_12144.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12138)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12131  in
                        mk uu____12130 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12168 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12168
               else
                 (let uu____12171 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12171 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12179 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12205  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12179 c1  in
                      let t2 =
                        let uu____12229 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12229 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12342)::uu____12343 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12356  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12358)::uu____12359 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12370  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12372,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12373;
                                   FStar_Syntax_Syntax.vars = uu____12374;_},uu____12375,uu____12376))::uu____12377
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12384  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12386)::uu____12387 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12398  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12400 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12403  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12408  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12434 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____12434
                         | FStar_Util.Inr c ->
                             let uu____12448 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____12448
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12471 =
                               let uu____12472 =
                                 let uu____12499 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12499, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12472
                                in
                             mk uu____12471 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____12534 ->
                           let uu____12535 =
                             let uu____12536 =
                               let uu____12537 =
                                 let uu____12564 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12564, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12537
                                in
                             mk uu____12536 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____12535))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                    &&
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weakly_reduce_scrutinee)
                   &&
                   (Prims.op_Negation
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak)
               then
                 let cfg' =
                   let uu___1577_12642 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1579_12645 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1579_12645.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1577_12642.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1577_12642.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1577_12642.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1577_12642.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1577_12642.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1577_12642.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1577_12642.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1577_12642.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 norm cfg' env ((Cfg cfg) :: stack1) head1
               else norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____12686 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12686 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1592_12706 = cfg  in
                               let uu____12707 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1592_12706.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____12707;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1592_12706.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1592_12706.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1592_12706.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1592_12706.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1592_12706.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1592_12706.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1592_12706.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____12714 =
                                 let uu____12715 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12715  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12714
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1599_12718 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1599_12718.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1599_12718.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1599_12718.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1599_12718.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12719 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12719
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12732,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12733;
                               FStar_Syntax_Syntax.lbunivs = uu____12734;
                               FStar_Syntax_Syntax.lbtyp = uu____12735;
                               FStar_Syntax_Syntax.lbeff = uu____12736;
                               FStar_Syntax_Syntax.lbdef = uu____12737;
                               FStar_Syntax_Syntax.lbattrs = uu____12738;
                               FStar_Syntax_Syntax.lbpos = uu____12739;_}::uu____12740),uu____12741)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12787 =
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.do_not_unfold_pure_lets)
                   &&
                   ((((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations
                        &&
                        (FStar_Syntax_Util.has_attribute
                           lb.FStar_Syntax_Syntax.lbattrs
                           FStar_Parser_Const.inline_let_attr))
                       ||
                       ((FStar_Syntax_Util.is_pure_effect n1) &&
                          (cfg.FStar_TypeChecker_Cfg.normalize_pure_lets ||
                             (FStar_Syntax_Util.has_attribute
                                lb.FStar_Syntax_Syntax.lbattrs
                                FStar_Parser_Const.inline_let_attr))))
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (Prims.op_Negation
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations)))
                  in
               if uu____12787
               then
                 let binder =
                   let uu____12791 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12791  in
                 let env1 =
                   let uu____12801 =
                     let uu____12808 =
                       let uu____12809 =
                         let uu____12841 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12841,
                           false)
                          in
                       Clos uu____12809  in
                     ((FStar_Pervasives_Native.Some binder), uu____12808)  in
                   uu____12801 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____12916  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____12923  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12925 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12925))
                 else
                   (let uu____12928 =
                      let uu____12933 =
                        let uu____12934 =
                          let uu____12941 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12941
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12934]  in
                      FStar_Syntax_Subst.open_term uu____12933 body  in
                    match uu____12928 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____12968  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12977 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12977  in
                            FStar_Util.Inl
                              (let uu___1641_12993 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1641_12993.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1641_12993.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____12996  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___1646_12999 = lb  in
                             let uu____13000 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1646_12999.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1646_12999.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____13000;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1646_12999.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1646_12999.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13029  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___1653_13054 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___1653_13054.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___1653_13054.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___1653_13054.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___1653_13054.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___1653_13054.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___1653_13054.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___1653_13054.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___1653_13054.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____13058  ->
                                FStar_Util.print_string
                                  "+++ Normalizing Tm_let -- body\n");
                           norm cfg1 env'
                             ((Let
                                 (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                             :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                 ||
                 ((Prims.op_Negation
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                    &&
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations)
               ->
               let uu____13079 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13079 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13115 =
                               let uu___1669_13116 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1669_13116.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1669_13116.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13115  in
                           let uu____13117 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13117 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13143 =
                                   FStar_List.map (fun uu____13159  -> dummy)
                                     lbs1
                                    in
                                 let uu____13160 =
                                   let uu____13169 =
                                     FStar_List.map
                                       (fun uu____13191  -> dummy) xs1
                                      in
                                   FStar_List.append uu____13169 env  in
                                 FStar_List.append uu____13143 uu____13160
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13217 =
                                       let uu___1683_13218 = rc  in
                                       let uu____13219 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1683_13218.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13219;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1683_13218.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13217
                                 | uu____13228 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1688_13234 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1688_13234.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1688_13234.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1688_13234.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1688_13234.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13244 =
                        FStar_List.map (fun uu____13260  -> dummy) lbs2  in
                      FStar_List.append uu____13244 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13268 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13268 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1697_13284 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1697_13284.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1697_13284.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____13318 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13318
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13339 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13417  ->
                        match uu____13417 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1713_13542 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1713_13542.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1713_13542.FStar_Syntax_Syntax.sort)
                              }  in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv  in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env  in
                            (rec_env1, (memo :: memos), (i + Prims.int_one)))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], Prims.int_zero)
                  in
               (match uu____13339 with
                | (rec_env,memos,uu____13733) ->
                    let uu____13788 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos
                       in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____14037 =
                               let uu____14044 =
                                 let uu____14045 =
                                   let uu____14077 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14077, false)
                                    in
                                 Clos uu____14045  in
                               (FStar_Pervasives_Native.None, uu____14044)
                                in
                             uu____14037 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14162  ->
                     let uu____14163 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14163);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14187 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14191::uu____14192 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14197) ->
                                 norm cfg env ((Meta (env, m, r)) :: stack)
                                   head1
                             | FStar_Syntax_Syntax.Meta_pattern (names1,args)
                                 ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 let names2 =
                                   FStar_All.pipe_right names1
                                     (FStar_List.map (norm cfg env []))
                                    in
                                 norm cfg env
                                   ((Meta
                                       (env,
                                         (FStar_Syntax_Syntax.Meta_pattern
                                            (names2, args1)),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____14276 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern
                                  (names1,args) ->
                                  let names2 =
                                    FStar_All.pipe_right names1
                                      (FStar_List.map (norm cfg env []))
                                     in
                                  let uu____14324 =
                                    let uu____14345 =
                                      norm_pattern_args cfg env args  in
                                    (names2, uu____14345)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14324
                              | uu____14374 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14380 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14404 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14418 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14432 =
                        let uu____14434 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14436 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14434 uu____14436
                         in
                      failwith uu____14432
                    else
                      (let uu____14441 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____14441)
                | uu____14442 -> norm cfg env stack t2))

and (do_unfold_fv :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Env.qninfo ->
            FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun qninfo  ->
            fun f  ->
              let uu____14451 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14451 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14465  ->
                        let uu____14466 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14466);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14479  ->
                        let uu____14480 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14482 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14480 uu____14482);
                   (let t1 =
                      if
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_until
                          =
                          (FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.delta_constant)
                      then t
                      else
                        FStar_Syntax_Subst.set_use_range
                          t0.FStar_Syntax_Syntax.pos t
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > Prims.int_zero
                    then
                      match stack with
                      | (UnivArgs (us',uu____14495))::stack1 ->
                          ((let uu____14504 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14504
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14512 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14512) us'
                            else ());
                           (let env1 =
                              FStar_All.pipe_right us'
                                (FStar_List.fold_left
                                   (fun env1  ->
                                      fun u  ->
                                        (FStar_Pervasives_Native.None,
                                          (Univ u))
                                        :: env1) env)
                               in
                            norm cfg env1 stack1 t1))
                      | uu____14548 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14551 ->
                          let uu____14554 =
                            let uu____14556 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14556
                             in
                          failwith uu____14554
                    else norm cfg env stack t1))

and (reduce_impure_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name *
                                            FStar_Syntax_Syntax.monad_name))
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun head1  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env [] t  in
              let stack1 = (Cfg cfg) :: stack  in
              let cfg1 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations
                then
                  let new_steps =
                    [FStar_TypeChecker_Env.PureSubtermsWithinComputations;
                    FStar_TypeChecker_Env.Primops;
                    FStar_TypeChecker_Env.AllowUnboundUniverses;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.Inlining]  in
                  let uu___1825_14584 = cfg  in
                  let uu____14585 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____14585;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1825_14584.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1825_14584.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1825_14584.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1825_14584.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1825_14584.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1825_14584.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___1825_14584.FStar_TypeChecker_Cfg.reifying)
                  }
                else cfg  in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1,m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1)
                 in
              norm cfg1 env
                ((Meta (env, metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1

and (do_reify_monadic :
  (unit -> FStar_Syntax_Syntax.term) ->
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun fallback  ->
    fun cfg  ->
      fun env  ->
        fun stack  ->
          fun head1  ->
            fun m  ->
              fun t  ->
                (match stack with
                 | (App
                     (uu____14616,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____14617;
                                    FStar_Syntax_Syntax.vars = uu____14618;_},uu____14619,uu____14620))::uu____14621
                     -> ()
                 | uu____14626 ->
                     let uu____14629 =
                       let uu____14631 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____14631
                        in
                     failwith uu____14629);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____14640  ->
                      let uu____14641 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____14643 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____14641
                        uu____14643);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____14647 =
                    let uu____14648 = FStar_Syntax_Subst.compress head3  in
                    uu____14648.FStar_Syntax_Syntax.n  in
                  match uu____14647 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____14669 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____14669
                         in
                      let uu____14670 = ed.FStar_Syntax_Syntax.bind_repr  in
                      (match uu____14670 with
                       | (uu____14671,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14681 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____14692 =
                                    let uu____14693 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14693.FStar_Syntax_Syntax.n  in
                                  match uu____14692 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____14699,uu____14700))
                                      ->
                                      let uu____14709 =
                                        let uu____14710 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____14710.FStar_Syntax_Syntax.n  in
                                      (match uu____14709 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____14716,msrc,uu____14718))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____14727 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____14727
                                       | uu____14728 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____14729 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____14730 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____14730 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___1897_14735 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___1897_14735.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___1897_14735.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___1897_14735.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___1897_14735.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___1897_14735.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____14736 = FStar_List.tl stack
                                        in
                                     let uu____14737 =
                                       let uu____14738 =
                                         let uu____14745 =
                                           let uu____14746 =
                                             let uu____14760 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____14760)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____14746
                                            in
                                         FStar_Syntax_Syntax.mk uu____14745
                                          in
                                       uu____14738
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____14736 uu____14737
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____14776 =
                                       let uu____14778 = is_return body  in
                                       match uu____14778 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____14783;
                                             FStar_Syntax_Syntax.vars =
                                               uu____14784;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____14787 -> false  in
                                     if uu____14776
                                     then
                                       norm cfg env stack
                                         lb.FStar_Syntax_Syntax.lbdef
                                     else
                                       (let rng =
                                          head3.FStar_Syntax_Syntax.pos  in
                                        let head4 =
                                          FStar_All.pipe_left
                                            FStar_Syntax_Util.mk_reify
                                            lb.FStar_Syntax_Syntax.lbdef
                                           in
                                        let body1 =
                                          FStar_All.pipe_left
                                            FStar_Syntax_Util.mk_reify body
                                           in
                                        let body_rc =
                                          {
                                            FStar_Syntax_Syntax.residual_effect
                                              = m;
                                            FStar_Syntax_Syntax.residual_typ
                                              =
                                              (FStar_Pervasives_Native.Some t);
                                            FStar_Syntax_Syntax.residual_flags
                                              = []
                                          }  in
                                        let body2 =
                                          let uu____14811 =
                                            let uu____14818 =
                                              let uu____14819 =
                                                let uu____14838 =
                                                  let uu____14847 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____14847]  in
                                                (uu____14838, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____14819
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____14818
                                             in
                                          uu____14811
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____14886 =
                                            let uu____14887 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____14887.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14886 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____14893::uu____14894::[])
                                              ->
                                              let uu____14899 =
                                                let uu____14906 =
                                                  let uu____14907 =
                                                    let uu____14914 =
                                                      let uu____14915 =
                                                        let uu____14916 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____14916
                                                         in
                                                      let uu____14917 =
                                                        let uu____14920 =
                                                          let uu____14921 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____14921
                                                           in
                                                        [uu____14920]  in
                                                      uu____14915 ::
                                                        uu____14917
                                                       in
                                                    (bind1, uu____14914)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____14907
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____14906
                                                 in
                                              uu____14899
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____14924 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____14939 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____14939
                                          then
                                            let uu____14952 =
                                              let uu____14961 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____14961
                                               in
                                            let uu____14962 =
                                              let uu____14973 =
                                                let uu____14982 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____14982
                                                 in
                                              [uu____14973]  in
                                            uu____14952 :: uu____14962
                                          else []  in
                                        let reified =
                                          let args =
                                            if
                                              ed.FStar_Syntax_Syntax.is_layered
                                            then
                                              let rest_bs =
                                                let uu____15051 =
                                                  let uu____15052 =
                                                    let uu____15055 =
                                                      FStar_All.pipe_right
                                                        ed.FStar_Syntax_Syntax.bind_wp
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15055
                                                      FStar_Syntax_Subst.compress
                                                     in
                                                  uu____15052.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____15051 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (uu____15078::uu____15079::bs,uu____15081)
                                                    when
                                                    (FStar_List.length bs) >=
                                                      (Prims.of_int (2))
                                                    ->
                                                    let uu____15133 =
                                                      FStar_All.pipe_right bs
                                                        (FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs)
                                                              -
                                                              (Prims.of_int (2))))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15133
                                                      FStar_Pervasives_Native.fst
                                                | uu____15239 ->
                                                    let uu____15240 =
                                                      let uu____15246 =
                                                        let uu____15248 =
                                                          FStar_Ident.string_of_lid
                                                            ed.FStar_Syntax_Syntax.mname
                                                           in
                                                        let uu____15250 =
                                                          let uu____15252 =
                                                            FStar_All.pipe_right
                                                              ed.FStar_Syntax_Syntax.bind_wp
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____15252
                                                            FStar_Syntax_Print.term_to_string
                                                           in
                                                        FStar_Util.format2
                                                          "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                          uu____15248
                                                          uu____15250
                                                         in
                                                      (FStar_Errors.Fatal_UnexpectedEffect,
                                                        uu____15246)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____15240 rng
                                                 in
                                              let uu____15276 =
                                                FStar_Syntax_Syntax.as_arg
                                                  lb.FStar_Syntax_Syntax.lbtyp
                                                 in
                                              let uu____15285 =
                                                let uu____15296 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____15305 =
                                                  let uu____15316 =
                                                    FStar_All.pipe_right
                                                      rest_bs
                                                      (FStar_List.map
                                                         (fun uu____15352  ->
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.unit_const))
                                                     in
                                                  let uu____15359 =
                                                    let uu____15370 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head4
                                                       in
                                                    let uu____15379 =
                                                      let uu____15390 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          body2
                                                         in
                                                      [uu____15390]  in
                                                    uu____15370 ::
                                                      uu____15379
                                                     in
                                                  FStar_List.append
                                                    uu____15316 uu____15359
                                                   in
                                                uu____15296 :: uu____15305
                                                 in
                                              uu____15276 :: uu____15285
                                            else
                                              (let uu____15449 =
                                                 let uu____15460 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____15469 =
                                                   let uu____15480 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   [uu____15480]  in
                                                 uu____15460 :: uu____15469
                                                  in
                                               let uu____15513 =
                                                 let uu____15524 =
                                                   let uu____15535 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       FStar_Syntax_Syntax.tun
                                                      in
                                                   let uu____15544 =
                                                     let uu____15555 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         head4
                                                        in
                                                     let uu____15564 =
                                                       let uu____15575 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           FStar_Syntax_Syntax.tun
                                                          in
                                                       let uu____15584 =
                                                         let uu____15595 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2
                                                            in
                                                         [uu____15595]  in
                                                       uu____15575 ::
                                                         uu____15584
                                                        in
                                                     uu____15555 ::
                                                       uu____15564
                                                      in
                                                   uu____15535 :: uu____15544
                                                    in
                                                 FStar_List.append
                                                   maybe_range_arg
                                                   uu____15524
                                                  in
                                               FStar_List.append uu____15449
                                                 uu____15513)
                                             in
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (bind_inst, args))
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____15676  ->
                                             let uu____15677 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____15679 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____15677 uu____15679);
                                        (let uu____15682 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____15682 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____15710 = FStar_Options.defensive ()  in
                        if uu____15710
                        then
                          let is_arg_impure uu____15725 =
                            match uu____15725 with
                            | (e,q) ->
                                let uu____15739 =
                                  let uu____15740 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____15740.FStar_Syntax_Syntax.n  in
                                (match uu____15739 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____15756 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____15756
                                 | uu____15758 -> false)
                             in
                          let uu____15760 =
                            let uu____15762 =
                              let uu____15773 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____15773 :: args  in
                            FStar_Util.for_some is_arg_impure uu____15762  in
                          (if uu____15760
                           then
                             let uu____15799 =
                               let uu____15805 =
                                 let uu____15807 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____15807
                                  in
                               (FStar_Errors.Warning_Defensive, uu____15805)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____15799
                           else ())
                        else ());
                       (let fallback1 uu____15820 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15824  ->
                               let uu____15825 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____15825 "");
                          (let uu____15829 = FStar_List.tl stack  in
                           let uu____15830 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____15829 uu____15830)
                           in
                        let fallback2 uu____15836 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15840  ->
                               let uu____15841 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____15841 "");
                          (let uu____15845 = FStar_List.tl stack  in
                           let uu____15846 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____15845 uu____15846)
                           in
                        let uu____15851 =
                          let uu____15852 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____15852.FStar_Syntax_Syntax.n  in
                        match uu____15851 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____15858 =
                              let uu____15860 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____15860  in
                            if uu____15858
                            then fallback1 ()
                            else
                              (let uu____15865 =
                                 let uu____15867 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____15867  in
                               if uu____15865
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____15884 =
                                      let uu____15889 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____15889 args
                                       in
                                    uu____15884 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____15890 = FStar_List.tl stack  in
                                  norm cfg env uu____15890 t1))
                        | uu____15891 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____15893) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____15917 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____15917  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____15921  ->
                            let uu____15922 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____15922);
                       (let uu____15925 = FStar_List.tl stack  in
                        norm cfg env uu____15925 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____16046  ->
                                match uu____16046 with
                                | (pat,wopt,tm) ->
                                    let uu____16094 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____16094)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____16126 = FStar_List.tl stack  in
                      norm cfg env uu____16126 tm
                  | uu____16127 -> fallback ()))

and (reify_lift :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.FStar_TypeChecker_Cfg.tcenv  in
            FStar_TypeChecker_Cfg.log cfg
              (fun uu____16141  ->
                 let uu____16142 = FStar_Ident.string_of_lid msrc  in
                 let uu____16144 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16146 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16142
                   uu____16144 uu____16146);
            (let uu____16149 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____16149
             then
               let ed =
                 let uu____16153 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____16153  in
               let uu____16154 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____16154 with
               | (uu____16155,return_repr) ->
                   let return_inst =
                     let uu____16168 =
                       let uu____16169 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____16169.FStar_Syntax_Syntax.n  in
                     match uu____16168 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16175::[]) ->
                         let uu____16180 =
                           let uu____16187 =
                             let uu____16188 =
                               let uu____16195 =
                                 let uu____16196 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____16196]  in
                               (return_tm, uu____16195)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____16188  in
                           FStar_Syntax_Syntax.mk uu____16187  in
                         uu____16180 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____16199 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let args =
                     if ed.FStar_Syntax_Syntax.is_layered
                     then
                       let rest_bs =
                         let uu____16234 =
                           let uu____16235 =
                             let uu____16238 =
                               FStar_All.pipe_right
                                 ed.FStar_Syntax_Syntax.ret_wp
                                 FStar_Pervasives_Native.snd
                                in
                             FStar_All.pipe_right uu____16238
                               FStar_Syntax_Subst.compress
                              in
                           uu____16235.FStar_Syntax_Syntax.n  in
                         match uu____16234 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             (uu____16261::bs,uu____16263) when
                             (FStar_List.length bs) >= Prims.int_one ->
                             let uu____16303 =
                               FStar_All.pipe_right bs
                                 (FStar_List.splitAt
                                    ((FStar_List.length bs) - Prims.int_one))
                                in
                             FStar_All.pipe_right uu____16303
                               FStar_Pervasives_Native.fst
                         | uu____16409 ->
                             let uu____16410 =
                               let uu____16416 =
                                 let uu____16418 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 let uu____16420 =
                                   let uu____16422 =
                                     FStar_All.pipe_right
                                       ed.FStar_Syntax_Syntax.ret_wp
                                       FStar_Pervasives_Native.snd
                                      in
                                   FStar_All.pipe_right uu____16422
                                     FStar_Syntax_Print.term_to_string
                                    in
                                 FStar_Util.format2
                                   "ret_wp for layered effect %s is not an arrow with >= 2 binders (%s)"
                                   uu____16418 uu____16420
                                  in
                               (FStar_Errors.Fatal_UnexpectedEffect,
                                 uu____16416)
                                in
                             FStar_Errors.raise_error uu____16410
                               e.FStar_Syntax_Syntax.pos
                          in
                       let uu____16446 = FStar_Syntax_Syntax.as_arg t  in
                       let uu____16455 =
                         let uu____16466 =
                           FStar_All.pipe_right rest_bs
                             (FStar_List.map
                                (fun uu____16502  ->
                                   FStar_Syntax_Syntax.as_arg
                                     FStar_Syntax_Syntax.unit_const))
                            in
                         let uu____16509 =
                           let uu____16520 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____16520]  in
                         FStar_List.append uu____16466 uu____16509  in
                       uu____16446 :: uu____16455
                     else
                       (let uu____16563 = FStar_Syntax_Syntax.as_arg t  in
                        let uu____16572 =
                          let uu____16583 = FStar_Syntax_Syntax.as_arg e  in
                          [uu____16583]  in
                        uu____16563 :: uu____16572)
                      in
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (return_inst, args))
                     FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
             else
               (let uu____16630 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____16630 with
                | FStar_Pervasives_Native.None  ->
                    let uu____16633 =
                      let uu____16635 = FStar_Ident.text_of_lid msrc  in
                      let uu____16637 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____16635 uu____16637
                       in
                    failwith uu____16633
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16640;
                      FStar_TypeChecker_Env.mtarget = uu____16641;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16642;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____16662 =
                      let uu____16664 = FStar_Ident.text_of_lid msrc  in
                      let uu____16666 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____16664 uu____16666
                       in
                    failwith uu____16662
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16669;
                      FStar_TypeChecker_Env.mtarget = uu____16670;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16671;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____16701 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____16702 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____16701 t uu____16702))

and (norm_pattern_args :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
          FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
          Prims.list Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____16772  ->
                   match uu____16772 with
                   | (a,imp) ->
                       let uu____16791 = norm cfg env [] a  in
                       (uu____16791, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____16801  ->
             let uu____16802 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____16804 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____16802 uu____16804);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16830 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _16833  -> FStar_Pervasives_Native.Some _16833)
                     uu____16830
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2071_16834 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2071_16834.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2071_16834.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16856 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _16859  -> FStar_Pervasives_Native.Some _16859)
                     uu____16856
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2082_16860 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2082_16860.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2082_16860.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____16905  ->
                      match uu____16905 with
                      | (a,i) ->
                          let uu____16925 = norm cfg env [] a  in
                          (uu____16925, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_16947  ->
                       match uu___14_16947 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____16951 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____16951
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2099_16959 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2101_16962 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2101_16962.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2099_16959.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2099_16959.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____16966 = b  in
        match uu____16966 with
        | (x,imp) ->
            let x1 =
              let uu___2109_16974 = x  in
              let uu____16975 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2109_16974.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2109_16974.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16975
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____16986 =
                    let uu____16987 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____16987  in
                  FStar_Pervasives_Native.Some uu____16986
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16998 =
          FStar_List.fold_left
            (fun uu____17032  ->
               fun b  ->
                 match uu____17032 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____16998 with | (nbs,uu____17112) -> FStar_List.rev nbs

and (norm_lcomp_opt :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____17144 =
              let uu___2134_17145 = rc  in
              let uu____17146 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2134_17145.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17146;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2134_17145.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17144
        | uu____17155 -> lopt

and (maybe_simplify :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.b380
          then
            (let uu____17165 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17167 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____17165 uu____17167)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_17179  ->
      match uu___15_17179 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17192 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____17192 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____17196 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____17196)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____17204 = norm_cb cfg  in
            reduce_primops uu____17204 cfg env tm  in
          let uu____17209 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____17209
          then tm1
          else
            (let w t =
               let uu___2162_17228 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2162_17228.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2162_17228.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17240 =
                 let uu____17241 = FStar_Syntax_Util.unmeta t  in
                 uu____17241.FStar_Syntax_Syntax.n  in
               match uu____17240 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17253 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17317)::args1,(bv,uu____17320)::bs1) ->
                   let uu____17374 =
                     let uu____17375 = FStar_Syntax_Subst.compress t  in
                     uu____17375.FStar_Syntax_Syntax.n  in
                   (match uu____17374 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17380 -> false)
               | ([],[]) -> true
               | (uu____17411,uu____17412) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17463 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17465 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17463
                    uu____17465)
               else ();
               (let uu____17470 = FStar_Syntax_Util.head_and_args' t  in
                match uu____17470 with
                | (hd1,args) ->
                    let uu____17509 =
                      let uu____17510 = FStar_Syntax_Subst.compress hd1  in
                      uu____17510.FStar_Syntax_Syntax.n  in
                    (match uu____17509 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____17518 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____17520 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____17522 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____17518 uu____17520 uu____17522)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____17527 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17545 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17547 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17545
                    uu____17547)
               else ();
               (let uu____17552 = FStar_Syntax_Util.is_squash t  in
                match uu____17552 with
                | FStar_Pervasives_Native.Some (uu____17563,t') ->
                    is_applied bs t'
                | uu____17575 ->
                    let uu____17584 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____17584 with
                     | FStar_Pervasives_Native.Some (uu____17595,t') ->
                         is_applied bs t'
                     | uu____17607 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____17631 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17631 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17638)::(q,uu____17640)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____17683 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____17685 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____17683 uu____17685)
                    else ();
                    (let uu____17690 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____17690 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17695 =
                           let uu____17696 = FStar_Syntax_Subst.compress p
                              in
                           uu____17696.FStar_Syntax_Syntax.n  in
                         (match uu____17695 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____17707 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17707))
                          | uu____17710 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____17713)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____17738 =
                           let uu____17739 = FStar_Syntax_Subst.compress p1
                              in
                           uu____17739.FStar_Syntax_Syntax.n  in
                         (match uu____17738 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____17750 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17750))
                          | uu____17753 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____17757 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____17757 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____17762 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____17762 with
                               | FStar_Pervasives_Native.Some bv' when
                                   FStar_Syntax_Syntax.bv_eq bv bv' ->
                                   (if
                                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                                    then
                                      FStar_Util.print_string "WPE> Case 3\n"
                                    else ();
                                    (let ftrue =
                                       FStar_Syntax_Util.abs bs
                                         FStar_Syntax_Util.t_true
                                         (FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Util.residual_tot
                                               FStar_Syntax_Util.ktype0))
                                        in
                                     let uu____17776 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17776))
                               | uu____17779 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____17784)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____17809 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____17809 with
                               | FStar_Pervasives_Native.Some bv' when
                                   FStar_Syntax_Syntax.bv_eq bv bv' ->
                                   (if
                                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                                    then
                                      FStar_Util.print_string "WPE> Case 4\n"
                                    else ();
                                    (let ffalse =
                                       FStar_Syntax_Util.abs bs
                                         FStar_Syntax_Util.t_false
                                         (FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Util.residual_tot
                                               FStar_Syntax_Util.ktype0))
                                        in
                                     let uu____17823 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17823))
                               | uu____17826 -> FStar_Pervasives_Native.None)
                          | uu____17829 -> FStar_Pervasives_Native.None)
                     | uu____17832 -> FStar_Pervasives_Native.None))
               | uu____17835 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____17848 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17848 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____17854)::[],uu____17855,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____17875 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____17877 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____17875
                         uu____17877)
                    else ();
                    is_quantified_const bv phi')
               | uu____17882 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____17897 =
                 let uu____17898 = FStar_Syntax_Subst.compress phi  in
                 uu____17898.FStar_Syntax_Syntax.n  in
               match uu____17897 with
               | FStar_Syntax_Syntax.Tm_match (uu____17904,br::brs) ->
                   let uu____17971 = br  in
                   (match uu____17971 with
                    | (uu____17989,uu____17990,e) ->
                        let r =
                          let uu____18012 = simp_t e  in
                          match uu____18012 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18024 =
                                FStar_List.for_all
                                  (fun uu____18043  ->
                                     match uu____18043 with
                                     | (uu____18057,uu____18058,e') ->
                                         let uu____18072 = simp_t e'  in
                                         uu____18072 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18024
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18088 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18098 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18098
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18136 =
                 match uu____18136 with
                 | (t1,q) ->
                     let uu____18157 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18157 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18189 -> (t1, q))
                  in
               let uu____18202 = FStar_Syntax_Util.head_and_args t  in
               match uu____18202 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18282 =
                 let uu____18283 = FStar_Syntax_Util.unmeta ty  in
                 uu____18283.FStar_Syntax_Syntax.n  in
               match uu____18282 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18288) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18293,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18317 -> false  in
             let simplify1 arg =
               let uu____18350 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18350, arg)  in
             let uu____18365 = is_forall_const tm1  in
             match uu____18365 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____18371 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18373 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18371
                       uu____18373)
                  else ();
                  (let uu____18378 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____18378))
             | FStar_Pervasives_Native.None  ->
                 let uu____18379 =
                   let uu____18380 = FStar_Syntax_Subst.compress tm1  in
                   uu____18380.FStar_Syntax_Syntax.n  in
                 (match uu____18379 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18384;
                              FStar_Syntax_Syntax.vars = uu____18385;_},uu____18386);
                         FStar_Syntax_Syntax.pos = uu____18387;
                         FStar_Syntax_Syntax.vars = uu____18388;_},args)
                      ->
                      let uu____18418 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18418
                      then
                        let uu____18421 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18421 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18479)::
                             (uu____18480,(arg,uu____18482))::[] ->
                             maybe_auto_squash arg
                         | (uu____18555,(arg,uu____18557))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18558)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18631)::uu____18632::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18702::(FStar_Pervasives_Native.Some (false
                                         ),uu____18703)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18773 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18791 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18791
                         then
                           let uu____18794 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18794 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18852)::uu____18853::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18923::(FStar_Pervasives_Native.Some (true
                                           ),uu____18924)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18994)::(uu____18995,(arg,uu____18997))::[]
                               -> maybe_auto_squash arg
                           | (uu____19070,(arg,uu____19072))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19073)::[]
                               -> maybe_auto_squash arg
                           | uu____19146 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19164 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19164
                            then
                              let uu____19167 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19167 with
                              | uu____19225::(FStar_Pervasives_Native.Some
                                              (true ),uu____19226)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19296)::uu____19297::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19367)::(uu____19368,(arg,uu____19370))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19443,(p,uu____19445))::(uu____19446,
                                                                (q,uu____19448))::[]
                                  ->
                                  let uu____19520 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19520
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19525 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19543 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19543
                               then
                                 let uu____19546 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19546 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19604)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19605)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19679)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19680)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19754)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19755)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19829)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19830)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19904,(arg,uu____19906))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19907)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19980)::(uu____19981,(arg,uu____19983))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20056,(arg,uu____20058))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20059)::[]
                                     ->
                                     let uu____20132 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20132
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20133)::(uu____20134,(arg,uu____20136))::[]
                                     ->
                                     let uu____20209 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20209
                                 | (uu____20210,(p,uu____20212))::(uu____20213,
                                                                   (q,uu____20215))::[]
                                     ->
                                     let uu____20287 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20287
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20292 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20310 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20310
                                  then
                                    let uu____20313 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20313 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20371)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20415)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20459 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20477 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20477
                                     then
                                       match args with
                                       | (t,uu____20481)::[] ->
                                           let uu____20506 =
                                             let uu____20507 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20507.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20506 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20510::[],body,uu____20512)
                                                ->
                                                let uu____20547 = simp_t body
                                                   in
                                                (match uu____20547 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20553 -> tm1)
                                            | uu____20557 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20559))::(t,uu____20561)::[]
                                           ->
                                           let uu____20601 =
                                             let uu____20602 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20602.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20601 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20605::[],body,uu____20607)
                                                ->
                                                let uu____20642 = simp_t body
                                                   in
                                                (match uu____20642 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20650 -> tm1)
                                            | uu____20654 -> tm1)
                                       | uu____20655 -> tm1
                                     else
                                       (let uu____20668 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20668
                                        then
                                          match args with
                                          | (t,uu____20672)::[] ->
                                              let uu____20697 =
                                                let uu____20698 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20698.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20697 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20701::[],body,uu____20703)
                                                   ->
                                                   let uu____20738 =
                                                     simp_t body  in
                                                   (match uu____20738 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20744 -> tm1)
                                               | uu____20748 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20750))::(t,uu____20752)::[]
                                              ->
                                              let uu____20792 =
                                                let uu____20793 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20793.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20792 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20796::[],body,uu____20798)
                                                   ->
                                                   let uu____20833 =
                                                     simp_t body  in
                                                   (match uu____20833 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____20841 -> tm1)
                                               | uu____20845 -> tm1)
                                          | uu____20846 -> tm1
                                        else
                                          (let uu____20859 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20859
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20862;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20863;_},uu____20864)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20890;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20891;_},uu____20892)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20918 -> tm1
                                           else
                                             (let uu____20931 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____20931
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____20945 =
                                                    let uu____20946 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____20946.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____20945 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____20957 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____20971 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____20971
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____21010 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____21010
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21016 =
                                                         let uu____21017 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____21017.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____21016 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21020 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____21028 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____21028
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____21037
                                                                  =
                                                                  let uu____21038
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____21038.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____21037
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____21044)
                                                                    -> hd1
                                                                | uu____21069
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____21073
                                                                =
                                                                let uu____21084
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____21084]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21073)
                                                       | uu____21117 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____21122 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____21122 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____21142 ->
                                                     let uu____21151 =
                                                       let uu____21158 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____21158 cfg env
                                                        in
                                                     uu____21151 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21164;
                         FStar_Syntax_Syntax.vars = uu____21165;_},args)
                      ->
                      let uu____21191 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21191
                      then
                        let uu____21194 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____21194 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21252)::
                             (uu____21253,(arg,uu____21255))::[] ->
                             maybe_auto_squash arg
                         | (uu____21328,(arg,uu____21330))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21331)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____21404)::uu____21405::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21475::(FStar_Pervasives_Native.Some (false
                                         ),uu____21476)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21546 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21564 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21564
                         then
                           let uu____21567 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21567 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21625)::uu____21626::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21696::(FStar_Pervasives_Native.Some (true
                                           ),uu____21697)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21767)::(uu____21768,(arg,uu____21770))::[]
                               -> maybe_auto_squash arg
                           | (uu____21843,(arg,uu____21845))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21846)::[]
                               -> maybe_auto_squash arg
                           | uu____21919 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21937 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21937
                            then
                              let uu____21940 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21940 with
                              | uu____21998::(FStar_Pervasives_Native.Some
                                              (true ),uu____21999)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22069)::uu____22070::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22140)::(uu____22141,(arg,uu____22143))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22216,(p,uu____22218))::(uu____22219,
                                                                (q,uu____22221))::[]
                                  ->
                                  let uu____22293 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22293
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22298 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22316 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22316
                               then
                                 let uu____22319 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____22319 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22377)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22378)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22452)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22453)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22527)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22528)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22602)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22603)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22677,(arg,uu____22679))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____22680)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22753)::(uu____22754,(arg,uu____22756))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____22829,(arg,uu____22831))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____22832)::[]
                                     ->
                                     let uu____22905 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22905
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22906)::(uu____22907,(arg,uu____22909))::[]
                                     ->
                                     let uu____22982 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22982
                                 | (uu____22983,(p,uu____22985))::(uu____22986,
                                                                   (q,uu____22988))::[]
                                     ->
                                     let uu____23060 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23060
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23065 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23083 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23083
                                  then
                                    let uu____23086 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23086 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23144)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23188)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23232 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23250 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23250
                                     then
                                       match args with
                                       | (t,uu____23254)::[] ->
                                           let uu____23279 =
                                             let uu____23280 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23280.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23279 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23283::[],body,uu____23285)
                                                ->
                                                let uu____23320 = simp_t body
                                                   in
                                                (match uu____23320 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23326 -> tm1)
                                            | uu____23330 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23332))::(t,uu____23334)::[]
                                           ->
                                           let uu____23374 =
                                             let uu____23375 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23375.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23374 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23378::[],body,uu____23380)
                                                ->
                                                let uu____23415 = simp_t body
                                                   in
                                                (match uu____23415 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____23423 -> tm1)
                                            | uu____23427 -> tm1)
                                       | uu____23428 -> tm1
                                     else
                                       (let uu____23441 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____23441
                                        then
                                          match args with
                                          | (t,uu____23445)::[] ->
                                              let uu____23470 =
                                                let uu____23471 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23471.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23470 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23474::[],body,uu____23476)
                                                   ->
                                                   let uu____23511 =
                                                     simp_t body  in
                                                   (match uu____23511 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____23517 -> tm1)
                                               | uu____23521 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____23523))::(t,uu____23525)::[]
                                              ->
                                              let uu____23565 =
                                                let uu____23566 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23566.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23565 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23569::[],body,uu____23571)
                                                   ->
                                                   let uu____23606 =
                                                     simp_t body  in
                                                   (match uu____23606 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____23614 -> tm1)
                                               | uu____23618 -> tm1)
                                          | uu____23619 -> tm1
                                        else
                                          (let uu____23632 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____23632
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23635;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23636;_},uu____23637)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23663;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23664;_},uu____23665)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____23691 -> tm1
                                           else
                                             (let uu____23704 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____23704
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____23718 =
                                                    let uu____23719 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____23719.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____23718 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____23730 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____23744 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____23744
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____23779 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____23779
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____23785 =
                                                         let uu____23786 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____23786.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____23785 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____23789 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____23797 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____23797
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____23806
                                                                  =
                                                                  let uu____23807
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____23807.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____23806
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____23813)
                                                                    -> hd1
                                                                | uu____23838
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____23842
                                                                =
                                                                let uu____23853
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____23853]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____23842)
                                                       | uu____23886 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____23891 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____23891 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____23911 ->
                                                     let uu____23920 =
                                                       let uu____23927 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____23927 cfg env
                                                        in
                                                     uu____23920 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____23938 = simp_t t  in
                      (match uu____23938 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____23947 ->
                      let uu____23970 = is_const_match tm1  in
                      (match uu____23970 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____23979 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____23989  ->
               (let uu____23991 = FStar_Syntax_Print.tag_of_term t  in
                let uu____23993 = FStar_Syntax_Print.term_to_string t  in
                let uu____23995 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____24003 =
                  let uu____24005 =
                    let uu____24008 = firstn (Prims.of_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24008
                     in
                  stack_to_string uu____24005  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____23991 uu____23993 uu____23995 uu____24003);
               (let uu____24033 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24033
                then
                  let uu____24037 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24037 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24044 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24046 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24048 =
                          let uu____24050 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24050
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24044
                          uu____24046 uu____24048);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____24072 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____24080)::uu____24081 -> true
                | uu____24091 -> false)
              in
           if uu____24072
           then
             let uu____24094 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____24094 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____24108 =
                        let uu____24110 =
                          let uu____24112 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____24112  in
                        FStar_Util.string_of_int uu____24110  in
                      let uu____24119 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____24121 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print3
                        "Normalized term (%s ms) %s\n\tto term %s\n"
                        uu____24108 uu____24119 uu____24121)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____24130,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24159  ->
                        let uu____24160 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____24160);
                   rebuild cfg env stack1 t1)
              | (Let (env',bs,lb,r))::stack1 ->
                  let body = FStar_Syntax_Subst.close bs t1  in
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env' stack1 t2
              | (Abs (env',bs,env'',lopt,r))::stack1 ->
                  let bs1 = norm_binders cfg env' bs  in
                  let lopt1 = norm_lcomp_opt cfg env'' lopt  in
                  let uu____24203 =
                    let uu___2791_24204 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2791_24204.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2791_24204.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____24203
              | (Arg (Univ uu____24207,uu____24208,uu____24209))::uu____24210
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____24214,uu____24215))::uu____24216 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____24232,uu____24233),aq,r))::stack1
                  when
                  let uu____24285 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24285 ->
                  let t2 =
                    let uu____24289 =
                      let uu____24294 =
                        let uu____24295 = closure_as_term cfg env_arg tm  in
                        (uu____24295, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____24294  in
                    uu____24289 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____24305),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24360  ->
                        let uu____24361 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____24361);
                   if
                     Prims.op_Negation
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                   then
                     (if
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                      then
                        let arg = closure_as_term cfg env_arg tm  in
                        let t2 =
                          FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                            FStar_Pervasives_Native.None r
                           in
                        rebuild cfg env_arg stack1 t2
                      else
                        (let stack2 = (App (env, t1, aq, r)) :: stack1  in
                         norm cfg env_arg stack2 tm))
                   else
                     (let uu____24381 = FStar_ST.op_Bang m  in
                      match uu____24381 with
                      | FStar_Pervasives_Native.None  ->
                          if
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                          then
                            let arg = closure_as_term cfg env_arg tm  in
                            let t2 =
                              FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                                FStar_Pervasives_Native.None r
                               in
                            rebuild cfg env_arg stack1 t2
                          else
                            (let stack2 = (MemoLazy m) ::
                               (App (env, t1, aq, r)) :: stack1  in
                             norm cfg env_arg stack2 tm)
                      | FStar_Pervasives_Native.Some (uu____24469,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____24525 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____24530  ->
                         let uu____24531 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____24531);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____24541 =
                    let uu____24542 = FStar_Syntax_Subst.compress t1  in
                    uu____24542.FStar_Syntax_Syntax.n  in
                  (match uu____24541 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____24570 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____24570  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____24574  ->
                             let uu____24575 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____24575);
                        (let uu____24578 = FStar_List.tl stack  in
                         norm cfg env1 uu____24578 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____24579);
                          FStar_Syntax_Syntax.pos = uu____24580;
                          FStar_Syntax_Syntax.vars = uu____24581;_},(e,uu____24583)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____24622 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____24639 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____24639 with
                        | (hd1,args) ->
                            let uu____24682 =
                              let uu____24683 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____24683.FStar_Syntax_Syntax.n  in
                            (match uu____24682 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____24687 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____24687 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____24690;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____24691;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____24692;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____24694;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____24695;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____24696;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____24697;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____24733 -> fallback " (3)" ())
                             | uu____24737 -> fallback " (4)" ()))
                   | uu____24739 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____24765  ->
                        let uu____24766 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____24766);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____24777 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____24782  ->
                           let uu____24783 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____24785 =
                             let uu____24787 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____24817  ->
                                       match uu____24817 with
                                       | (p,uu____24828,uu____24829) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____24787
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____24783 uu____24785);
                      (let whnf =
                         (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                           ||
                           (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                          in
                       let cfg_exclude_zeta =
                         let new_delta =
                           FStar_All.pipe_right
                             cfg1.FStar_TypeChecker_Cfg.delta_level
                             (FStar_List.filter
                                (fun uu___16_24851  ->
                                   match uu___16_24851 with
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                        -> true
                                   | uu____24855 -> false))
                            in
                         let steps =
                           let uu___2959_24858 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___2959_24858.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___2962_24865 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___2962_24865.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___2962_24865.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___2962_24865.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___2962_24865.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___2962_24865.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___2962_24865.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____24940 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____24971 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____25060  ->
                                       fun uu____25061  ->
                                         match (uu____25060, uu____25061)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____25211 =
                                               norm_pat env3 p1  in
                                             (match uu____25211 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____24971 with
                              | (pats1,env3) ->
                                  ((let uu___2990_25381 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___2990_25381.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___2994_25402 = x  in
                               let uu____25403 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2994_25402.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2994_25402.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25403
                               }  in
                             ((let uu___2997_25417 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___2997_25417.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3001_25428 = x  in
                               let uu____25429 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3001_25428.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3001_25428.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25429
                               }  in
                             ((let uu___3004_25443 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3004_25443.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3010_25459 = x  in
                               let uu____25460 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3010_25459.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3010_25459.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25460
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___3014_25475 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3014_25475.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____25519 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____25549 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____25549 with
                                     | (p,wopt,e) ->
                                         let uu____25569 = norm_pat env1 p
                                            in
                                         (match uu____25569 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____25624 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____25624
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____25641 =
                           ((((cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                                &&
                                (Prims.op_Negation
                                   (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak))
                               &&
                               (Prims.op_Negation
                                  (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars))
                              &&
                              (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weakly_reduce_scrutinee)
                             && (maybe_weakly_reduced scrutinee)
                            in
                         if uu____25641
                         then
                           norm
                             (let uu___3033_25648 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3035_25651 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3035_25651.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3033_25648.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3033_25648.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3033_25648.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3033_25648.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3033_25648.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3033_25648.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3033_25648.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3033_25648.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____25655 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____25655)
                       in
                    let rec is_cons head1 =
                      let uu____25681 =
                        let uu____25682 = FStar_Syntax_Subst.compress head1
                           in
                        uu____25682.FStar_Syntax_Syntax.n  in
                      match uu____25681 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____25687) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____25692 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____25694;
                            FStar_Syntax_Syntax.fv_delta = uu____25695;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____25697;
                            FStar_Syntax_Syntax.fv_delta = uu____25698;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____25699);_}
                          -> true
                      | uu____25707 -> false  in
                    let guard_when_clause wopt b rest =
                      match wopt with
                      | FStar_Pervasives_Native.None  -> b
                      | FStar_Pervasives_Native.Some w ->
                          let then_branch = b  in
                          let else_branch =
                            mk
                              (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                              r
                             in
                          FStar_Syntax_Util.if_then_else w then_branch
                            else_branch
                       in
                    let rec matches_pat scrutinee_orig p =
                      let scrutinee1 =
                        FStar_Syntax_Util.unmeta scrutinee_orig  in
                      let scrutinee2 = FStar_Syntax_Util.unlazy scrutinee1
                         in
                      let uu____25876 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____25876 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____25973 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____26015 ->
                                    let uu____26016 =
                                      let uu____26018 = is_cons head1  in
                                      Prims.op_Negation uu____26018  in
                                    FStar_Util.Inr uu____26016)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____26047 =
                                 let uu____26048 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____26048.FStar_Syntax_Syntax.n  in
                               (match uu____26047 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____26067 ->
                                    let uu____26068 =
                                      let uu____26070 = is_cons head1  in
                                      Prims.op_Negation uu____26070  in
                                    FStar_Util.Inr uu____26068))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____26161)::rest_a,(p1,uu____26164)::rest_p)
                          ->
                          let uu____26223 = matches_pat t2 p1  in
                          (match uu____26223 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____26276 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____26399 = matches_pat scrutinee1 p1  in
                          (match uu____26399 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____26445  ->
                                     let uu____26446 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____26448 =
                                       let uu____26450 =
                                         FStar_List.map
                                           (fun uu____26462  ->
                                              match uu____26462 with
                                              | (uu____26468,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____26450
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____26446 uu____26448);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____26504  ->
                                          match uu____26504 with
                                          | (bv,t2) ->
                                              let uu____26527 =
                                                let uu____26534 =
                                                  let uu____26537 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____26537
                                                   in
                                                let uu____26538 =
                                                  let uu____26539 =
                                                    let uu____26571 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____26571,
                                                      false)
                                                     in
                                                  Clos uu____26539  in
                                                (uu____26534, uu____26538)
                                                 in
                                              uu____26527 :: env2) env1 s
                                    in
                                 let uu____26664 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____26664)))
                       in
                    if
                      (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                    then matches scrutinee branches
                    else norm_and_rebuild_match ()))))

let (normalize_with_primitive_steps :
  FStar_TypeChecker_Cfg.primitive_step Prims.list ->
    FStar_TypeChecker_Env.steps ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = FStar_TypeChecker_Cfg.config' ps s e  in
          FStar_TypeChecker_Cfg.log_cfg c
            (fun uu____26697  ->
               let uu____26698 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____26698);
          (let uu____26701 = is_nbe_request s  in
           if uu____26701
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____26707  ->
                   let uu____26708 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____26708);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____26714  ->
                   let uu____26715 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____26715);
              (let uu____26718 =
                 FStar_Util.record_time (fun uu____26725  -> nbe_eval c s t)
                  in
               match uu____26718 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____26734  ->
                         let uu____26735 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____26737 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____26735 uu____26737);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____26745  ->
                   let uu____26746 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____26746);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____26752  ->
                   let uu____26753 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____26753);
              (let uu____26756 =
                 FStar_Util.record_time (fun uu____26763  -> norm c [] [] t)
                  in
               match uu____26756 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____26778  ->
                         let uu____26779 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____26781 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____26779 uu____26781);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____26800 =
          let uu____26804 =
            let uu____26806 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____26806  in
          FStar_Pervasives_Native.Some uu____26804  in
        FStar_Profiling.profile
          (fun uu____26809  -> normalize_with_primitive_steps [] s e t)
          uu____26800 "FStar.TypeChecker.Normalize"
  
let (normalize_comp :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____26827 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____26827 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____26845 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____26845 [] u
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      let cfg =
        FStar_TypeChecker_Cfg.config
          [FStar_TypeChecker_Env.UnfoldUntil
             FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.AllowUnboundUniverses;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.Unascribe;
          FStar_TypeChecker_Env.ForExtraction] env
         in
      let non_info t =
        let uu____26871 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____26871  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____26878 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___3192_26897 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3192_26897.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3192_26897.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____26904 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____26904
          then
            let ct1 =
              let uu____26908 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____26908 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____26915 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____26915
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3202_26922 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3202_26922.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3202_26922.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3202_26922.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___3206_26924 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3206_26924.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3206_26924.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3206_26924.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3206_26924.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3209_26925 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3209_26925.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3209_26925.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____26928 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      let cfg =
        FStar_TypeChecker_Cfg.config
          [FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses;
          FStar_TypeChecker_Env.Unascribe;
          FStar_TypeChecker_Env.ForExtraction] env
         in
      let non_info t =
        let uu____26948 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____26948  in
      let uu____26955 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____26955
      then
        let uu____26958 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____26958 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3220_26962 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3220_26962.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3220_26962.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3220_26962.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3227_26981  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3226_26984 ->
            ((let uu____26986 =
                let uu____26992 =
                  let uu____26994 = FStar_Util.message_of_exn uu___3226_26984
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____26994
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____26992)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____26986);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3237_27013  ->
             match () with
             | () ->
                 let uu____27014 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____27014 [] c) ()
        with
        | uu___3236_27023 ->
            ((let uu____27025 =
                let uu____27031 =
                  let uu____27033 = FStar_Util.message_of_exn uu___3236_27023
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27033
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27031)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27025);
             c)
         in
      FStar_Syntax_Print.comp_to_string' env.FStar_TypeChecker_Env.dsenv c1
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t =
          normalize (FStar_List.append steps [FStar_TypeChecker_Env.Beta])
            env t0
           in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1  in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort  in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____27082 =
                     let uu____27083 =
                       let uu____27090 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27090)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27083  in
                   mk uu____27082 t01.FStar_Syntax_Syntax.pos
               | uu____27095 -> t2)
          | uu____27096 -> t2  in
        aux t
  
let (whnf_steps : FStar_TypeChecker_Env.step Prims.list) =
  [FStar_TypeChecker_Env.Primops;
  FStar_TypeChecker_Env.Weak;
  FStar_TypeChecker_Env.HNF;
  FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
  FStar_TypeChecker_Env.Beta] 
let (unfold_whnf' :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t  -> normalize (FStar_List.append steps whnf_steps) env t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> unfold_whnf' [] env t 
let (reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append
             (if remove then [FStar_TypeChecker_Env.CheckNoUvars] else [])
             [FStar_TypeChecker_Env.Beta;
             FStar_TypeChecker_Env.DoNotUnfoldPureLets;
             FStar_TypeChecker_Env.CompressUvars;
             FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
             FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Iota;
             FStar_TypeChecker_Env.NoFullNorm]) env t
  
let (reduce_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t 
let (remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t 
let (eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____27190 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27190 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27227 ->
                 let uu____27236 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27236 with
                  | (actuals,uu____27246,uu____27247) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27267 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27267 with
                         | (binders,args) ->
                             let uu____27278 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27278
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
  
let (eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____27293 ->
          let uu____27294 = FStar_Syntax_Util.head_and_args t  in
          (match uu____27294 with
           | (head1,args) ->
               let uu____27337 =
                 let uu____27338 = FStar_Syntax_Subst.compress head1  in
                 uu____27338.FStar_Syntax_Syntax.n  in
               (match uu____27337 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____27359 =
                      let uu____27374 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____27374  in
                    (match uu____27359 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____27414 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3307_27422 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3307_27422.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3307_27422.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3307_27422.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3307_27422.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3307_27422.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3307_27422.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3307_27422.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3307_27422.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3307_27422.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___3307_27422.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3307_27422.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3307_27422.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3307_27422.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3307_27422.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3307_27422.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3307_27422.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3307_27422.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3307_27422.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3307_27422.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3307_27422.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3307_27422.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3307_27422.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3307_27422.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3307_27422.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3307_27422.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3307_27422.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3307_27422.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3307_27422.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3307_27422.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3307_27422.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3307_27422.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3307_27422.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3307_27422.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3307_27422.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3307_27422.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3307_27422.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3307_27422.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3307_27422.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3307_27422.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3307_27422.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3307_27422.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3307_27422.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3307_27422.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____27414 with
                            | (uu____27425,ty,uu____27427) ->
                                eta_expand_with_type env t ty))
                | uu____27428 ->
                    let uu____27429 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3314_27437 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3314_27437.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3314_27437.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3314_27437.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3314_27437.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3314_27437.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3314_27437.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3314_27437.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3314_27437.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3314_27437.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___3314_27437.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3314_27437.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3314_27437.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3314_27437.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3314_27437.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3314_27437.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3314_27437.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3314_27437.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3314_27437.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3314_27437.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3314_27437.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3314_27437.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3314_27437.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3314_27437.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3314_27437.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3314_27437.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3314_27437.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3314_27437.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3314_27437.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3314_27437.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3314_27437.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3314_27437.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3314_27437.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3314_27437.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3314_27437.FStar_TypeChecker_Env.try_solve_implicits_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3314_27437.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3314_27437.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3314_27437.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3314_27437.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3314_27437.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3314_27437.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3314_27437.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3314_27437.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3314_27437.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____27429 with
                     | (uu____27440,ty,uu____27442) ->
                         eta_expand_with_type env t ty)))
  
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
       in
    let t1 = FStar_Syntax_Subst.compress t  in
    let elim_bv x =
      let uu___3326_27524 = x  in
      let uu____27525 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3326_27524.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3326_27524.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____27525
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____27528 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____27552 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____27553 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____27554 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____27555 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____27562 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____27563 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____27564 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3352_27598 = rc  in
          let uu____27599 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____27608 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3352_27598.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____27599;
            FStar_Syntax_Syntax.residual_flags = uu____27608
          }  in
        let uu____27611 =
          let uu____27612 =
            let uu____27631 = elim_delayed_subst_binders bs  in
            let uu____27640 = elim_delayed_subst_term t2  in
            let uu____27643 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____27631, uu____27640, uu____27643)  in
          FStar_Syntax_Syntax.Tm_abs uu____27612  in
        mk1 uu____27611
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____27680 =
          let uu____27681 =
            let uu____27696 = elim_delayed_subst_binders bs  in
            let uu____27705 = elim_delayed_subst_comp c  in
            (uu____27696, uu____27705)  in
          FStar_Syntax_Syntax.Tm_arrow uu____27681  in
        mk1 uu____27680
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____27724 =
          let uu____27725 =
            let uu____27732 = elim_bv bv  in
            let uu____27733 = elim_delayed_subst_term phi  in
            (uu____27732, uu____27733)  in
          FStar_Syntax_Syntax.Tm_refine uu____27725  in
        mk1 uu____27724
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____27764 =
          let uu____27765 =
            let uu____27782 = elim_delayed_subst_term t2  in
            let uu____27785 = elim_delayed_subst_args args  in
            (uu____27782, uu____27785)  in
          FStar_Syntax_Syntax.Tm_app uu____27765  in
        mk1 uu____27764
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3374_27857 = p  in
              let uu____27858 =
                let uu____27859 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____27859  in
              {
                FStar_Syntax_Syntax.v = uu____27858;
                FStar_Syntax_Syntax.p =
                  (uu___3374_27857.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3378_27861 = p  in
              let uu____27862 =
                let uu____27863 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____27863  in
              {
                FStar_Syntax_Syntax.v = uu____27862;
                FStar_Syntax_Syntax.p =
                  (uu___3378_27861.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3384_27870 = p  in
              let uu____27871 =
                let uu____27872 =
                  let uu____27879 = elim_bv x  in
                  let uu____27880 = elim_delayed_subst_term t0  in
                  (uu____27879, uu____27880)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____27872  in
              {
                FStar_Syntax_Syntax.v = uu____27871;
                FStar_Syntax_Syntax.p =
                  (uu___3384_27870.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3390_27905 = p  in
              let uu____27906 =
                let uu____27907 =
                  let uu____27921 =
                    FStar_List.map
                      (fun uu____27947  ->
                         match uu____27947 with
                         | (x,b) ->
                             let uu____27964 = elim_pat x  in
                             (uu____27964, b)) pats
                     in
                  (fv, uu____27921)  in
                FStar_Syntax_Syntax.Pat_cons uu____27907  in
              {
                FStar_Syntax_Syntax.v = uu____27906;
                FStar_Syntax_Syntax.p =
                  (uu___3390_27905.FStar_Syntax_Syntax.p)
              }
          | uu____27979 -> p  in
        let elim_branch uu____28003 =
          match uu____28003 with
          | (pat,wopt,t3) ->
              let uu____28029 = elim_pat pat  in
              let uu____28032 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28035 = elim_delayed_subst_term t3  in
              (uu____28029, uu____28032, uu____28035)
           in
        let uu____28040 =
          let uu____28041 =
            let uu____28064 = elim_delayed_subst_term t2  in
            let uu____28067 = FStar_List.map elim_branch branches  in
            (uu____28064, uu____28067)  in
          FStar_Syntax_Syntax.Tm_match uu____28041  in
        mk1 uu____28040
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28198 =
          match uu____28198 with
          | (tc,topt) ->
              let uu____28233 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28243 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28243
                | FStar_Util.Inr c ->
                    let uu____28245 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28245
                 in
              let uu____28246 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28233, uu____28246)
           in
        let uu____28255 =
          let uu____28256 =
            let uu____28283 = elim_delayed_subst_term t2  in
            let uu____28286 = elim_ascription a  in
            (uu____28283, uu____28286, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28256  in
        mk1 uu____28255
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3420_28349 = lb  in
          let uu____28350 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____28353 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3420_28349.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3420_28349.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____28350;
            FStar_Syntax_Syntax.lbeff =
              (uu___3420_28349.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____28353;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3420_28349.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3420_28349.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____28356 =
          let uu____28357 =
            let uu____28371 =
              let uu____28379 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____28379)  in
            let uu____28391 = elim_delayed_subst_term t2  in
            (uu____28371, uu____28391)  in
          FStar_Syntax_Syntax.Tm_let uu____28357  in
        mk1 uu____28356
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____28436 =
          let uu____28437 =
            let uu____28444 = elim_delayed_subst_term tm  in
            (uu____28444, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____28437  in
        mk1 uu____28436
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____28455 =
          let uu____28456 =
            let uu____28463 = elim_delayed_subst_term t2  in
            let uu____28466 = elim_delayed_subst_meta md  in
            (uu____28463, uu____28466)  in
          FStar_Syntax_Syntax.Tm_meta uu____28456  in
        mk1 uu____28455

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_28475  ->
         match uu___17_28475 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____28479 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____28479
         | f -> f) flags

and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos
       in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____28502 =
          let uu____28503 =
            let uu____28512 = elim_delayed_subst_term t  in
            (uu____28512, uopt)  in
          FStar_Syntax_Syntax.Total uu____28503  in
        mk1 uu____28502
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____28529 =
          let uu____28530 =
            let uu____28539 = elim_delayed_subst_term t  in
            (uu____28539, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____28530  in
        mk1 uu____28529
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3453_28548 = ct  in
          let uu____28549 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____28552 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____28563 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3453_28548.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3453_28548.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____28549;
            FStar_Syntax_Syntax.effect_args = uu____28552;
            FStar_Syntax_Syntax.flags = uu____28563
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_28566  ->
    match uu___18_28566 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____28601 =
          let uu____28622 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____28631 = FStar_List.map elim_delayed_subst_args args  in
          (uu____28622, uu____28631)  in
        FStar_Syntax_Syntax.Meta_pattern uu____28601
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____28686 =
          let uu____28693 = elim_delayed_subst_term t  in (m, uu____28693)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____28686
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____28705 =
          let uu____28714 = elim_delayed_subst_term t  in
          (m1, m2, uu____28714)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____28705
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
    Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____28747  ->
         match uu____28747 with
         | (t,q) ->
             let uu____28766 = elim_delayed_subst_term t  in (uu____28766, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____28794  ->
         match uu____28794 with
         | (x,q) ->
             let uu____28813 =
               let uu___3479_28814 = x  in
               let uu____28815 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3479_28814.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3479_28814.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____28815
               }  in
             (uu____28813, q)) bs

let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list *
            (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.comp'
                                                                    FStar_Syntax_Syntax.syntax)
            FStar_Util.either))
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____28923,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____28955,FStar_Util.Inl t) ->
                let uu____28977 =
                  let uu____28984 =
                    let uu____28985 =
                      let uu____29000 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29000)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____28985  in
                  FStar_Syntax_Syntax.mk uu____28984  in
                uu____28977 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29013 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29013 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29045 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29118 ->
                    let uu____29119 =
                      let uu____29128 =
                        let uu____29129 = FStar_Syntax_Subst.compress t4  in
                        uu____29129.FStar_Syntax_Syntax.n  in
                      (uu____29128, tc)  in
                    (match uu____29119 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29158) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29205) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29250,FStar_Util.Inl uu____29251) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29282 -> failwith "Impossible")
                 in
              (match uu____29045 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list * FStar_Syntax_Syntax.term'
            FStar_Syntax_Syntax.syntax))
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____29421 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____29421 with
          | (univ_names1,binders1,tc) ->
              let uu____29495 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____29495)
  
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list * FStar_Syntax_Syntax.comp'
            FStar_Syntax_Syntax.syntax))
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____29549 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____29549 with
          | (univ_names1,binders1,tc) ->
              let uu____29623 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____29623)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____29665 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____29665 with
           | (univ_names1,binders1,typ1) ->
               let uu___3562_29705 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3562_29705.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3562_29705.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3562_29705.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3562_29705.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3568_29720 = s  in
          let uu____29721 =
            let uu____29722 =
              let uu____29731 = FStar_List.map (elim_uvars env) sigs  in
              (uu____29731, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____29722  in
          {
            FStar_Syntax_Syntax.sigel = uu____29721;
            FStar_Syntax_Syntax.sigrng =
              (uu___3568_29720.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3568_29720.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3568_29720.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3568_29720.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____29750 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29750 with
           | (univ_names1,uu____29774,typ1) ->
               let uu___3582_29796 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3582_29796.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3582_29796.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3582_29796.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3582_29796.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____29803 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29803 with
           | (univ_names1,uu____29827,typ1) ->
               let uu___3593_29849 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3593_29849.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3593_29849.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3593_29849.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3593_29849.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____29879 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____29879 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____29904 =
                            let uu____29905 =
                              let uu____29906 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____29906  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____29905
                             in
                          elim_delayed_subst_term uu____29904  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3609_29909 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3609_29909.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3609_29909.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3609_29909.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3609_29909.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3612_29910 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3612_29910.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3612_29910.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3612_29910.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3612_29910.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3616_29917 = s  in
          let uu____29918 =
            let uu____29919 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____29919  in
          {
            FStar_Syntax_Syntax.sigel = uu____29918;
            FStar_Syntax_Syntax.sigrng =
              (uu___3616_29917.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3616_29917.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3616_29917.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3616_29917.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____29923 = elim_uvars_aux_t env us [] t  in
          (match uu____29923 with
           | (us1,uu____29947,t1) ->
               let uu___3627_29969 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3627_29969.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3627_29969.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3627_29969.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3627_29969.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____29970 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____29973 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____29973 with
           | (univs1,binders,uu____29992) ->
               let uu____30013 =
                 let uu____30018 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____30018 with
                 | (univs_opening,univs2) ->
                     let uu____30041 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____30041)
                  in
               (match uu____30013 with
                | (univs_opening,univs_closing) ->
                    let uu____30044 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30050 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30051 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30050, uu____30051)  in
                    (match uu____30044 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30077 =
                           match uu____30077 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30095 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30095 with
                                | (us1,t1) ->
                                    let uu____30106 =
                                      let uu____30115 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30120 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30115, uu____30120)  in
                                    (match uu____30106 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30143 =
                                           let uu____30152 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____30157 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____30152, uu____30157)  in
                                         (match uu____30143 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30181 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30181
                                                 in
                                              let uu____30182 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____30182 with
                                               | (uu____30209,uu____30210,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30233 =
                                                       let uu____30234 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30234
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30233
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30243 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____30243 with
                           | (uu____30262,uu____30263,t1) -> t1  in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ((a.FStar_Syntax_Syntax.action_defn),
                                      ((FStar_Util.Inl
                                          (a.FStar_Syntax_Syntax.action_typ)),
                                        FStar_Pervasives_Native.None),
                                      FStar_Pervasives_Native.None))
                                 FStar_Pervasives_Native.None
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____30339 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____30366 =
                               let uu____30367 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____30367.FStar_Syntax_Syntax.n  in
                             match uu____30366 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____30426 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____30460 =
                               let uu____30461 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____30461.FStar_Syntax_Syntax.n  in
                             match uu____30460 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____30484) ->
                                 let uu____30509 = destruct_action_body body
                                    in
                                 (match uu____30509 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____30558 ->
                                 let uu____30559 = destruct_action_body t  in
                                 (match uu____30559 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____30614 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____30614 with
                           | (action_univs,t) ->
                               let uu____30623 = destruct_action_typ_templ t
                                  in
                               (match uu____30623 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3713_30670 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3713_30670.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3713_30670.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      }  in
                                    a')
                            in
                         let ed1 =
                           let uu___3716_30672 = ed  in
                           let uu____30673 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____30674 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____30675 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____30676 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____30677 =
                             FStar_Syntax_Util.map_match_wps elim_tscheme
                               ed.FStar_Syntax_Syntax.match_wps
                              in
                           let uu____30682 =
                             FStar_Util.map_opt
                               ed.FStar_Syntax_Syntax.trivial elim_tscheme
                              in
                           let uu____30685 =
                             elim_tscheme ed.FStar_Syntax_Syntax.repr  in
                           let uu____30686 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____30687 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____30688 =
                             FStar_Util.map_opt
                               ed.FStar_Syntax_Syntax.stronger_repr
                               elim_tscheme
                              in
                           let uu____30691 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.is_layered =
                               (uu___3716_30672.FStar_Syntax_Syntax.is_layered);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3716_30672.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___3716_30672.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____30673;
                             FStar_Syntax_Syntax.ret_wp = uu____30674;
                             FStar_Syntax_Syntax.bind_wp = uu____30675;
                             FStar_Syntax_Syntax.stronger = uu____30676;
                             FStar_Syntax_Syntax.match_wps = uu____30677;
                             FStar_Syntax_Syntax.trivial = uu____30682;
                             FStar_Syntax_Syntax.repr = uu____30685;
                             FStar_Syntax_Syntax.return_repr = uu____30686;
                             FStar_Syntax_Syntax.bind_repr = uu____30687;
                             FStar_Syntax_Syntax.stronger_repr = uu____30688;
                             FStar_Syntax_Syntax.actions = uu____30691;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3716_30672.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3719_30694 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3719_30694.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3719_30694.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3719_30694.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3719_30694.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_30715 =
            match uu___19_30715 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____30746 = elim_uvars_aux_t env us [] t  in
                (match uu____30746 with
                 | (us1,uu____30778,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3734_30809 = sub_eff  in
            let uu____30810 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____30813 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3734_30809.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3734_30809.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____30810;
              FStar_Syntax_Syntax.lift = uu____30813
            }  in
          let uu___3737_30816 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3737_30816.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3737_30816.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3737_30816.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3737_30816.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____30826 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____30826 with
           | (univ_names1,binders1,comp1) ->
               let uu___3750_30866 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3750_30866.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3750_30866.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3750_30866.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3750_30866.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____30869 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____30870 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.AllowUnboundUniverses] env t
  
let (unfold_head_once :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let aux f us args =
        let uu____30919 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____30919 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____30941 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____30941 with
             | (uu____30948,head_def) ->
                 let t' =
                   FStar_Syntax_Syntax.mk_Tm_app head_def args
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                    in
                 let t'1 =
                   normalize
                     [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota]
                     env t'
                    in
                 FStar_Pervasives_Native.Some t'1)
         in
      let uu____30954 = FStar_Syntax_Util.head_and_args t  in
      match uu____30954 with
      | (head1,args) ->
          let uu____30999 =
            let uu____31000 = FStar_Syntax_Subst.compress head1  in
            uu____31000.FStar_Syntax_Syntax.n  in
          (match uu____30999 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____31007;
                  FStar_Syntax_Syntax.vars = uu____31008;_},us)
               -> aux fv us args
           | uu____31014 -> FStar_Pervasives_Native.None)
  