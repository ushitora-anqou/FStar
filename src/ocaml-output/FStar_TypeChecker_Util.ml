open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_TypeChecker_Common.lcomp)
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____22 = FStar_TypeChecker_Env.get_range env  in
      let uu____23 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.log_issue uu____22 uu____23
  
let (new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar *
            FStar_Range.range) Prims.list * FStar_TypeChecker_Common.guard_t))
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          FStar_TypeChecker_Env.new_implicit_var_aux reason r env k
            FStar_Syntax_Syntax.Strict FStar_Pervasives_Native.None
  
let (close_guard_implicits :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun solve_deferred  ->
      fun xs  ->
        fun g  ->
          let uu____87 = (FStar_Options.eager_subtyping ()) || solve_deferred
             in
          if uu____87
          then
            let uu____90 =
              FStar_All.pipe_right g.FStar_TypeChecker_Common.deferred
                (FStar_List.partition
                   (fun uu____142  ->
                      match uu____142 with
                      | (uu____149,p) ->
                          FStar_TypeChecker_Rel.flex_prob_closing env xs p))
               in
            match uu____90 with
            | (solve_now,defer) ->
                ((let uu____184 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel")
                     in
                  if uu____184
                  then
                    (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                     FStar_List.iter
                       (fun uu____201  ->
                          match uu____201 with
                          | (s,p) ->
                              let uu____211 =
                                FStar_TypeChecker_Rel.prob_to_string env p
                                 in
                              FStar_Util.print2 "%s: %s\n" s uu____211)
                       solve_now;
                     FStar_Util.print_string " ...DEFERRED THE REST:\n";
                     FStar_List.iter
                       (fun uu____226  ->
                          match uu____226 with
                          | (s,p) ->
                              let uu____236 =
                                FStar_TypeChecker_Rel.prob_to_string env p
                                 in
                              FStar_Util.print2 "%s: %s\n" s uu____236) defer;
                     FStar_Util.print_string "END\n")
                  else ());
                 (let g1 =
                    FStar_TypeChecker_Rel.solve_deferred_constraints env
                      (let uu___49_244 = g  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___49_244.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred_to_tac =
                           (uu___49_244.FStar_TypeChecker_Common.deferred_to_tac);
                         FStar_TypeChecker_Common.deferred = solve_now;
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___49_244.FStar_TypeChecker_Common.univ_ineqs);
                         FStar_TypeChecker_Common.implicits =
                           (uu___49_244.FStar_TypeChecker_Common.implicits)
                       })
                     in
                  let g2 =
                    let uu___52_246 = g1  in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___52_246.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred_to_tac =
                        (uu___52_246.FStar_TypeChecker_Common.deferred_to_tac);
                      FStar_TypeChecker_Common.deferred = defer;
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___52_246.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits =
                        (uu___52_246.FStar_TypeChecker_Common.implicits)
                    }  in
                  g2))
          else g
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____263 =
        let uu____265 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____265  in
      if uu____263
      then
        let us =
          let uu____270 =
            let uu____274 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____274
             in
          FStar_All.pipe_right uu____270 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____293 =
            let uu____299 =
              let uu____301 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____301
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____299)  in
          FStar_Errors.log_issue r uu____293);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env  ->
    fun uu____324  ->
      match uu____324 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____335;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____337;
          FStar_Syntax_Syntax.lbpos = uu____338;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____373 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____373 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____411) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____418) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____473) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____509 = FStar_Options.ml_ish ()  in
                                if uu____509
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____531 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____531
                            then
                              let uu____534 = FStar_Range.string_of_range r
                                 in
                              let uu____536 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____534 uu____536
                            else ());
                           FStar_Util.Inl t2)
                      | uu____541 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____543 = aux e1  in
                      match uu____543 with
                      | FStar_Util.Inr c ->
                          let uu____549 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____549
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____554 =
                               let uu____560 =
                                 let uu____562 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____562
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____560)
                                in
                             FStar_Errors.raise_error uu____554 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____571 ->
               let uu____572 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____572 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
  
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun pat  ->
    let mk1 f =
      FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None
        pat.FStar_Syntax_Syntax.p
       in
    let pat_as_arg uu____636 =
      match uu____636 with
      | (p,i) ->
          let uu____656 = decorated_pattern_as_term p  in
          (match uu____656 with
           | (vars,te) ->
               let uu____679 =
                 let uu____684 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____684)  in
               (vars, uu____679))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____698 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____698)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____702 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____702)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____706 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____706)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____729 =
          let uu____748 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____748 FStar_List.unzip  in
        (match uu____729 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____886 =
               let uu____887 =
                 let uu____888 =
                   let uu____905 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____905, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____888  in
               mk1 uu____887  in
             (vars1, uu____886))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____944,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____954,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____968 -> FStar_Pervasives_Native.Some hd1)
  
let (lcomp_univ_opt :
  FStar_TypeChecker_Common.lcomp ->
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option *
      FStar_TypeChecker_Common.guard_t))
  =
  fun lc  ->
    let uu____983 =
      FStar_All.pipe_right lc FStar_TypeChecker_Common.lcomp_comp  in
    FStar_All.pipe_right uu____983
      (fun uu____1011  ->
         match uu____1011 with | (c,g) -> ((comp_univ_opt c), g))
  
let (destruct_wp_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  = fun c  -> FStar_Syntax_Util.destruct_comp c 
let (mk_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags  ->
            let uu____1084 =
              let uu____1085 =
                let uu____1096 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1096]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1085;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1084
  
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let (effect_args_from_repr :
  FStar_Syntax_Syntax.term ->
    Prims.bool -> FStar_Range.range -> FStar_Syntax_Syntax.term Prims.list)
  =
  fun repr  ->
    fun is_layered1  ->
      fun r  ->
        let err uu____1180 =
          let uu____1181 =
            let uu____1187 =
              let uu____1189 = FStar_Syntax_Print.term_to_string repr  in
              let uu____1191 = FStar_Util.string_of_bool is_layered1  in
              FStar_Util.format2
                "Could not get effect args from repr %s with is_layered %s"
                uu____1189 uu____1191
               in
            (FStar_Errors.Fatal_UnexpectedEffect, uu____1187)  in
          FStar_Errors.raise_error uu____1181 r  in
        let repr1 = FStar_Syntax_Subst.compress repr  in
        if is_layered1
        then
          match repr1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_app (uu____1203,uu____1204::is) ->
              FStar_All.pipe_right is
                (FStar_List.map FStar_Pervasives_Native.fst)
          | uu____1272 -> err ()
        else
          (match repr1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (uu____1277,c) ->
               let uu____1299 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_to_comp_typ
                  in
               FStar_All.pipe_right uu____1299
                 (fun ct  ->
                    FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                      (FStar_List.map FStar_Pervasives_Native.fst))
           | uu____1334 -> err ())
  
let (mk_wp_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun e  ->
            fun r  ->
              let ret_wp =
                FStar_All.pipe_right ed
                  FStar_Syntax_Util.get_return_vc_combinator
                 in
              let wp =
                let uu____1370 =
                  let uu____1375 =
                    FStar_TypeChecker_Env.inst_effect_fun_with [u_a] env ed
                      ret_wp
                     in
                  let uu____1376 =
                    let uu____1377 = FStar_Syntax_Syntax.as_arg a  in
                    let uu____1386 =
                      let uu____1397 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____1397]  in
                    uu____1377 :: uu____1386  in
                  FStar_Syntax_Syntax.mk_Tm_app uu____1375 uu____1376  in
                uu____1370 FStar_Pervasives_Native.None r  in
              mk_comp ed u_a a wp [FStar_Syntax_Syntax.RETURN]
  
let (mk_indexed_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Range.range ->
              (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun e  ->
            fun r  ->
              (let uu____1470 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____1470
               then
                 let uu____1475 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
                 let uu____1477 = FStar_Syntax_Print.univ_to_string u_a  in
                 let uu____1479 = FStar_Syntax_Print.term_to_string a  in
                 let uu____1481 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print4
                   "Computing %s.return for u_a:%s, a:%s, and e:%s{\n"
                   uu____1475 uu____1477 uu____1479 uu____1481
               else ());
              (let uu____1486 =
                 let uu____1491 =
                   FStar_All.pipe_right ed
                     FStar_Syntax_Util.get_return_vc_combinator
                    in
                 FStar_TypeChecker_Env.inst_tscheme_with uu____1491 [u_a]  in
               match uu____1486 with
               | (uu____1496,return_t) ->
                   let return_t_shape_error s =
                     let uu____1511 =
                       let uu____1513 =
                         FStar_Ident.string_of_lid
                           ed.FStar_Syntax_Syntax.mname
                          in
                       let uu____1515 =
                         FStar_Syntax_Print.term_to_string return_t  in
                       FStar_Util.format3
                         "%s.return %s does not have proper shape (reason:%s)"
                         uu____1513 uu____1515 s
                        in
                     (FStar_Errors.Fatal_UnexpectedEffect, uu____1511)  in
                   let uu____1519 =
                     let uu____1548 =
                       let uu____1549 = FStar_Syntax_Subst.compress return_t
                          in
                       uu____1549.FStar_Syntax_Syntax.n  in
                     match uu____1548 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                         (FStar_List.length bs) >= (Prims.of_int (2)) ->
                         let uu____1609 = FStar_Syntax_Subst.open_comp bs c
                            in
                         (match uu____1609 with
                          | (a_b::x_b::bs1,c1) ->
                              let uu____1678 =
                                FStar_Syntax_Util.comp_to_comp_typ c1  in
                              (a_b, x_b, bs1, uu____1678))
                     | uu____1699 ->
                         let uu____1700 =
                           return_t_shape_error
                             "Either not an arrow or not enough binders"
                            in
                         FStar_Errors.raise_error uu____1700 r
                      in
                   (match uu____1519 with
                    | (a_b,x_b,rest_bs,return_ct) ->
                        let uu____1783 =
                          let uu____1790 =
                            let uu____1791 =
                              let uu____1792 =
                                let uu____1799 =
                                  FStar_All.pipe_right a_b
                                    FStar_Pervasives_Native.fst
                                   in
                                (uu____1799, a)  in
                              FStar_Syntax_Syntax.NT uu____1792  in
                            let uu____1810 =
                              let uu____1813 =
                                let uu____1814 =
                                  let uu____1821 =
                                    FStar_All.pipe_right x_b
                                      FStar_Pervasives_Native.fst
                                     in
                                  (uu____1821, e)  in
                                FStar_Syntax_Syntax.NT uu____1814  in
                              [uu____1813]  in
                            uu____1791 :: uu____1810  in
                          FStar_TypeChecker_Env.uvars_for_binders env rest_bs
                            uu____1790
                            (fun b  ->
                               let uu____1837 =
                                 FStar_Syntax_Print.binder_to_string b  in
                               let uu____1839 =
                                 let uu____1841 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Util.format1 "%s.return" uu____1841
                                  in
                               let uu____1844 = FStar_Range.string_of_range r
                                  in
                               FStar_Util.format3
                                 "implicit var for binder %s of %s at %s"
                                 uu____1837 uu____1839 uu____1844) r
                           in
                        (match uu____1783 with
                         | (rest_bs_uvars,g_uvars) ->
                             let subst1 =
                               FStar_List.map2
                                 (fun b  ->
                                    fun t  ->
                                      let uu____1881 =
                                        let uu____1888 =
                                          FStar_All.pipe_right b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____1888, t)  in
                                      FStar_Syntax_Syntax.NT uu____1881) (a_b
                                 :: x_b :: rest_bs) (a :: e :: rest_bs_uvars)
                                in
                             let is =
                               let uu____1914 =
                                 let uu____1917 =
                                   FStar_Syntax_Subst.compress
                                     return_ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 let uu____1918 =
                                   FStar_Syntax_Util.is_layered ed  in
                                 effect_args_from_repr uu____1917 uu____1918
                                   r
                                  in
                               FStar_All.pipe_right uu____1914
                                 (FStar_List.map
                                    (FStar_Syntax_Subst.subst subst1))
                                in
                             let c =
                               let uu____1925 =
                                 let uu____1926 =
                                   FStar_All.pipe_right is
                                     (FStar_List.map
                                        FStar_Syntax_Syntax.as_arg)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs = [u_a];
                                   FStar_Syntax_Syntax.effect_name =
                                     (ed.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.result_typ = a;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____1926;
                                   FStar_Syntax_Syntax.flags = []
                                 }  in
                               FStar_Syntax_Syntax.mk_Comp uu____1925  in
                             ((let uu____1950 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____1950
                               then
                                 let uu____1955 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.print1 "} c after return %s\n"
                                   uu____1955
                               else ());
                              (c, g_uvars)))))
  
let (mk_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Range.range ->
              (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun e  ->
            fun r  ->
              let uu____1999 =
                FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
              if uu____1999
              then mk_indexed_return env ed u_a a e r
              else
                (let uu____2009 = mk_wp_return env ed u_a a e r  in
                 (uu____2009, FStar_TypeChecker_Env.trivial_guard))
  
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.mlift ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun lift  ->
        let uu____2034 =
          FStar_All.pipe_right
            (let uu___251_2036 = c  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___251_2036.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___251_2036.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___251_2036.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___251_2036.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = []
             }) FStar_Syntax_Syntax.mk_Comp
           in
        FStar_All.pipe_right uu____2034
          (lift.FStar_TypeChecker_Env.mlift_wp env)
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1_in  ->
      fun l2_in  ->
        let uu____2057 =
          let uu____2062 = FStar_TypeChecker_Env.norm_eff_name env l1_in  in
          let uu____2063 = FStar_TypeChecker_Env.norm_eff_name env l2_in  in
          (uu____2062, uu____2063)  in
        match uu____2057 with
        | (l1,l2) ->
            let uu____2066 = FStar_TypeChecker_Env.join_opt env l1 l2  in
            (match uu____2066 with
             | FStar_Pervasives_Native.Some (m,uu____2076,uu____2077) -> m
             | FStar_Pervasives_Native.None  ->
                 let uu____2090 =
                   FStar_TypeChecker_Env.exists_polymonadic_bind env l1 l2
                    in
                 (match uu____2090 with
                  | FStar_Pervasives_Native.Some (m,uu____2104) -> m
                  | FStar_Pervasives_Native.None  ->
                      let uu____2137 =
                        let uu____2143 =
                          let uu____2145 =
                            FStar_Syntax_Print.lid_to_string l1_in  in
                          let uu____2147 =
                            FStar_Syntax_Print.lid_to_string l2_in  in
                          FStar_Util.format2
                            "Effects %s and %s cannot be composed" uu____2145
                            uu____2147
                           in
                        (FStar_Errors.Fatal_EffectsCannotBeComposed,
                          uu____2143)
                         in
                      FStar_Errors.raise_error uu____2137
                        env.FStar_TypeChecker_Env.range))
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2167 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____2167
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_TypeChecker_Common.eff_name
            c2.FStar_TypeChecker_Common.eff_name
  
let (lift_comps_sep_guards :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          Prims.bool ->
            (FStar_Ident.lident * FStar_Syntax_Syntax.comp *
              FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t *
              FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        fun b  ->
          fun for_bind  ->
            let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
            let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
            let uu____2226 =
              FStar_TypeChecker_Env.join_opt env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name
               in
            match uu____2226 with
            | FStar_Pervasives_Native.Some (m,lift1,lift2) ->
                let uu____2254 = lift_comp env c11 lift1  in
                (match uu____2254 with
                 | (c12,g1) ->
                     let uu____2271 =
                       if Prims.op_Negation for_bind
                       then lift_comp env c21 lift2
                       else
                         (let x_a =
                            match b with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Syntax.null_binder
                                  (FStar_Syntax_Util.comp_result c12)
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Syntax.mk_binder x
                             in
                          let env_x =
                            FStar_TypeChecker_Env.push_binders env [x_a]  in
                          let uu____2310 = lift_comp env_x c21 lift2  in
                          match uu____2310 with
                          | (c22,g2) ->
                              let uu____2321 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2
                                 in
                              (c22, uu____2321))
                        in
                     (match uu____2271 with
                      | (c22,g2) -> (m, c12, c22, g1, g2)))
            | FStar_Pervasives_Native.None  ->
                let rng = env.FStar_TypeChecker_Env.range  in
                let err uu____2368 =
                  let uu____2369 =
                    let uu____2375 =
                      let uu____2377 =
                        FStar_Syntax_Print.lid_to_string
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2379 =
                        FStar_Syntax_Print.lid_to_string
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____2377
                        uu____2379
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____2375)
                     in
                  FStar_Errors.raise_error uu____2369 rng  in
                ((let uu____2394 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "LayeredEffects")
                     in
                  if uu____2394
                  then
                    let uu____2399 =
                      let uu____2401 =
                        FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2401
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2403 =
                      let uu____2405 =
                        FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2405
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2407 = FStar_Util.string_of_bool for_bind  in
                    FStar_Util.print3
                      "Lifting comps %s and %s with for_bind %s{\n"
                      uu____2399 uu____2403 uu____2407
                  else ());
                 if for_bind
                 then err ()
                 else
                   (let bind_with_return ct ret_eff f_bind =
                      let x_bv =
                        FStar_Syntax_Syntax.gen_bv "x"
                          FStar_Pervasives_Native.None
                          ct.FStar_Syntax_Syntax.result_typ
                         in
                      let uu____2463 =
                        let uu____2468 =
                          FStar_TypeChecker_Env.push_bv env x_bv  in
                        let uu____2469 =
                          FStar_TypeChecker_Env.get_effect_decl env ret_eff
                           in
                        let uu____2470 =
                          FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
                        let uu____2471 = FStar_Syntax_Syntax.bv_to_name x_bv
                           in
                        mk_return uu____2468 uu____2469 uu____2470
                          ct.FStar_Syntax_Syntax.result_typ uu____2471 rng
                         in
                      match uu____2463 with
                      | (c_ret,g_ret) ->
                          let uu____2478 =
                            let uu____2483 =
                              FStar_Syntax_Util.comp_to_comp_typ c_ret  in
                            f_bind env ct (FStar_Pervasives_Native.Some x_bv)
                              uu____2483 [] rng
                             in
                          (match uu____2478 with
                           | (c,g_bind) ->
                               let uu____2490 =
                                 FStar_TypeChecker_Env.conj_guard g_ret
                                   g_bind
                                  in
                               (c, uu____2490))
                       in
                    let try_lift c12 c22 =
                      let p_bind_opt =
                        FStar_TypeChecker_Env.exists_polymonadic_bind env
                          c12.FStar_Syntax_Syntax.effect_name
                          c22.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2535 =
                        FStar_All.pipe_right p_bind_opt FStar_Util.is_some
                         in
                      if uu____2535
                      then
                        let uu____2571 =
                          FStar_All.pipe_right p_bind_opt FStar_Util.must  in
                        match uu____2571 with
                        | (p,f_bind) ->
                            let uu____2638 =
                              FStar_Ident.lid_equals p
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            (if uu____2638
                             then
                               let uu____2651 = bind_with_return c12 p f_bind
                                  in
                               match uu____2651 with
                               | (c13,g) ->
                                   let uu____2668 =
                                     let uu____2677 =
                                       FStar_Syntax_Syntax.mk_Comp c22  in
                                     ((c22.FStar_Syntax_Syntax.effect_name),
                                       c13, uu____2677, g)
                                      in
                                   FStar_Pervasives_Native.Some uu____2668
                             else FStar_Pervasives_Native.None)
                      else FStar_Pervasives_Native.None  in
                    let uu____2706 =
                      let uu____2717 = try_lift c11 c21  in
                      match uu____2717 with
                      | FStar_Pervasives_Native.Some (p,c12,c22,g) ->
                          (p, c12, c22, g,
                            FStar_TypeChecker_Env.trivial_guard)
                      | FStar_Pervasives_Native.None  ->
                          let uu____2758 = try_lift c21 c11  in
                          (match uu____2758 with
                           | FStar_Pervasives_Native.Some (p,c22,c12,g) ->
                               (p, c12, c22,
                                 FStar_TypeChecker_Env.trivial_guard, g)
                           | FStar_Pervasives_Native.None  -> err ())
                       in
                    match uu____2706 with
                    | (p,c12,c22,g1,g2) ->
                        ((let uu____2815 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2815
                          then
                            let uu____2820 = FStar_Ident.string_of_lid p  in
                            let uu____2822 =
                              FStar_Syntax_Print.comp_to_string c12  in
                            let uu____2824 =
                              FStar_Syntax_Print.comp_to_string c22  in
                            FStar_Util.print3
                              "} Returning p %s, c1 %s, and c2 %s\n"
                              uu____2820 uu____2822 uu____2824
                          else ());
                         (p, c12, c22, g1, g2))))
  
let (lift_comps :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          Prims.bool ->
            (FStar_Ident.lident * FStar_Syntax_Syntax.comp *
              FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        fun b  ->
          fun for_bind  ->
            let uu____2877 = lift_comps_sep_guards env c1 c2 b for_bind  in
            match uu____2877 with
            | (l,c11,c21,g1,g2) ->
                let uu____2901 = FStar_TypeChecker_Env.conj_guard g1 g2  in
                (l, c11, c21, uu____2901)
  
let (is_pure_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid
  
let (is_pure_or_ghost_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)
  
let (lax_mk_tot_or_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun flags  ->
          let uu____2957 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2957
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2969 =
      let uu____2970 = FStar_Syntax_Subst.compress t  in
      uu____2970.FStar_Syntax_Syntax.n  in
    match uu____2969 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2974 -> true
    | uu____2990 -> false
  
let (label :
  Prims.string ->
    FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun reason  ->
    fun r  ->
      fun f  ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_meta
             (f, (FStar_Syntax_Syntax.Meta_labeled (reason, r, false))))
          FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos
  
let (label_opt :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun reason  ->
      fun r  ->
        fun f  ->
          match reason with
          | FStar_Pervasives_Native.None  -> f
          | FStar_Pervasives_Native.Some reason1 ->
              let uu____3060 =
                let uu____3062 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____3062  in
              if uu____3060
              then f
              else (let uu____3069 = reason1 ()  in label uu____3069 r f)
  
let (label_guard :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun r  ->
    fun reason  ->
      fun g  ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___396_3090 = g  in
            let uu____3091 =
              let uu____3092 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____3092  in
            {
              FStar_TypeChecker_Common.guard_f = uu____3091;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___396_3090.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___396_3090.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___396_3090.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___396_3090.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____3113 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____3113
        then c
        else
          (let uu____3118 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____3118
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close1 =
                  let uu____3160 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____3160 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____3188 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____3188]  in
                       let us =
                         let uu____3210 =
                           let uu____3213 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____3213]  in
                         u_res :: uu____3210  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____3219 =
                         let uu____3224 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md close1
                            in
                         let uu____3225 =
                           let uu____3226 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____3235 =
                             let uu____3246 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____3255 =
                               let uu____3266 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____3266]  in
                             uu____3246 :: uu____3255  in
                           uu____3226 :: uu____3235  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3224 uu____3225
                          in
                       uu____3219 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____3308 = destruct_wp_comp c1  in
              match uu____3308 with
              | (u_res_t,res_t,wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name
                     in
                  let wp1 = close_wp u_res_t md res_t bvs wp  in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
  
let (close_wp_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        let bs =
          FStar_All.pipe_right bvs
            (FStar_List.map FStar_Syntax_Syntax.mk_binder)
           in
        FStar_All.pipe_right lc
          (FStar_TypeChecker_Common.apply_lcomp (close_wp_comp env bvs)
             (fun g  ->
                let uu____3348 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____3348
                  (close_guard_implicits env false bs)))
  
let (close_layered_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun tms  ->
        fun lc  ->
          let bs =
            FStar_All.pipe_right bvs
              (FStar_List.map FStar_Syntax_Syntax.mk_binder)
             in
          let substs =
            FStar_List.map2
              (fun bv  -> fun tm  -> FStar_Syntax_Syntax.NT (bv, tm)) bvs tms
             in
          FStar_All.pipe_right lc
            (FStar_TypeChecker_Common.apply_lcomp
               (FStar_Syntax_Subst.subst_comp substs)
               (fun g  ->
                  let uu____3398 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____3398
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_3411  ->
            match uu___0_3411 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____3414 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____3439 =
            let uu____3442 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____3442 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____3439
            (fun c  ->
               (let uu____3466 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____3466) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3470 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____3470)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3481 = FStar_Syntax_Util.head_and_args' e  in
                match uu____3481 with
                | (head1,uu____3498) ->
                    let uu____3519 =
                      let uu____3520 = FStar_Syntax_Util.un_uinst head1  in
                      uu____3520.FStar_Syntax_Syntax.n  in
                    (match uu____3519 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3525 =
                           let uu____3527 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3527
                            in
                         Prims.op_Negation uu____3525
                     | uu____3528 -> true)))
              &&
              (let uu____3531 = should_not_inline_lc lc  in
               Prims.op_Negation uu____3531)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v1  ->
          let c =
            let uu____3559 =
              let uu____3561 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3561  in
            if uu____3559
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3568 = FStar_Syntax_Util.is_unit t  in
               if uu____3568
               then
                 FStar_Syntax_Syntax.mk_Total' t
                   (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.U_zero)
               else
                 (let m =
                    FStar_TypeChecker_Env.get_effect_decl env
                      FStar_Parser_Const.effect_PURE_lid
                     in
                  let u_t =
                    match u_t_opt with
                    | FStar_Pervasives_Native.None  ->
                        env.FStar_TypeChecker_Env.universe_of env t
                    | FStar_Pervasives_Native.Some u_t -> u_t  in
                  let wp =
                    let uu____3577 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3577
                    then FStar_Syntax_Syntax.tun
                    else
                      (let ret_wp =
                         FStar_All.pipe_right m
                           FStar_Syntax_Util.get_return_vc_combinator
                          in
                       let uu____3583 =
                         let uu____3584 =
                           let uu____3589 =
                             FStar_TypeChecker_Env.inst_effect_fun_with 
                               [u_t] env m ret_wp
                              in
                           let uu____3590 =
                             let uu____3591 = FStar_Syntax_Syntax.as_arg t
                                in
                             let uu____3600 =
                               let uu____3611 = FStar_Syntax_Syntax.as_arg v1
                                  in
                               [uu____3611]  in
                             uu____3591 :: uu____3600  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3589
                             uu____3590
                            in
                         uu____3584 FStar_Pervasives_Native.None
                           v1.FStar_Syntax_Syntax.pos
                          in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.Beta;
                         FStar_TypeChecker_Env.NoFullNorm] env uu____3583)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3645 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3645
           then
             let uu____3650 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____3652 = FStar_Syntax_Print.term_to_string v1  in
             let uu____3654 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3650 uu____3652 uu____3654
           else ());
          c
  
let (mk_indexed_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme ->
            FStar_Syntax_Syntax.comp_typ ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Syntax_Syntax.comp_typ ->
                  FStar_Syntax_Syntax.cflag Prims.list ->
                    FStar_Range.range ->
                      (FStar_Syntax_Syntax.comp *
                        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun bind_t  ->
            fun ct1  ->
              fun b  ->
                fun ct2  ->
                  fun flags  ->
                    fun r1  ->
                      (let uu____3727 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____3727
                       then
                         let uu____3732 =
                           let uu____3734 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____3734  in
                         let uu____3735 =
                           let uu____3737 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____3737  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3732 uu____3735
                       else ());
                      (let uu____3742 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "ResolveImplicitsHook")
                          in
                       if uu____3742
                       then
                         let uu____3747 =
                           let uu____3749 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Range.string_of_range uu____3749  in
                         let uu____3750 =
                           FStar_Syntax_Print.tscheme_to_string bind_t  in
                         FStar_Util.print2
                           "///////////////////////////////Bind at %s/////////////////////\nwith bind_t = %s\n"
                           uu____3747 uu____3750
                       else ());
                      (let uu____3755 =
                         let uu____3762 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____3763 =
                           FStar_TypeChecker_Env.get_effect_decl env n1  in
                         let uu____3764 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____3762, uu____3763, uu____3764)  in
                       match uu____3755 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____3772 =
                             let uu____3785 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3786 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3785,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3786)
                              in
                           (match uu____3772 with
                            | (u1,t1,is1) ->
                                let uu____3830 =
                                  let uu____3843 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3844 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3843,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3844)
                                   in
                                (match uu____3830 with
                                 | (u2,t2,is2) ->
                                     let uu____3888 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3888 with
                                      | (uu____3897,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3912 =
                                              let uu____3914 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____3914 s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3912)
                                             in
                                          let uu____3918 =
                                            let uu____3963 =
                                              let uu____3964 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3964.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3963 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____4040 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____4040 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____4125 =
                                                       let uu____4152 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____4152
                                                         (fun uu____4237  ->
                                                            match uu____4237
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____4318
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____4331
                                                                  =
                                                                  let uu____4338
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____4338
                                                                   in
                                                                (l1,
                                                                  uu____4318,
                                                                  uu____4331))
                                                        in
                                                     (match uu____4125 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4498 ->
                                                let uu____4499 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4499 r1
                                             in
                                          (match uu____3918 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_c)
                                               ->
                                               let uu____4624 =
                                                 let uu____4631 =
                                                   let uu____4632 =
                                                     let uu____4633 =
                                                       let uu____4640 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4640, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4633
                                                      in
                                                   let uu____4651 =
                                                     let uu____4654 =
                                                       let uu____4655 =
                                                         let uu____4662 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4662, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4655
                                                        in
                                                     [uu____4654]  in
                                                   uu____4632 :: uu____4651
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4631
                                                   (fun b1  ->
                                                      let uu____4678 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4680 =
                                                        let uu____4682 =
                                                          FStar_Ident.string_of_lid
                                                            m
                                                           in
                                                        let uu____4684 =
                                                          FStar_Ident.string_of_lid
                                                            n1
                                                           in
                                                        let uu____4686 =
                                                          FStar_Ident.string_of_lid
                                                            p
                                                           in
                                                        FStar_Util.format3
                                                          "(%s, %s) |> %s"
                                                          uu____4682
                                                          uu____4684
                                                          uu____4686
                                                         in
                                                      let uu____4689 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4678 uu____4680
                                                        uu____4689) r1
                                                  in
                                               (match uu____4624 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    ((let uu____4703 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "ResolveImplicitsHook")
                                                         in
                                                      if uu____4703
                                                      then
                                                        FStar_All.pipe_right
                                                          rest_bs_uvars
                                                          (FStar_List.iter
                                                             (fun t  ->
                                                                let uu____4717
                                                                  =
                                                                  let uu____4718
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    t  in
                                                                  uu____4718.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____4717
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (u,uu____4722)
                                                                    ->
                                                                    let uu____4739
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t  in
                                                                    let uu____4741
                                                                    =
                                                                    match 
                                                                    u.FStar_Syntax_Syntax.ctx_uvar_meta
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                                                    a) ->
                                                                    FStar_Syntax_Print.term_to_string
                                                                    a
                                                                    | 
                                                                    uu____4747
                                                                    ->
                                                                    "<no attr>"
                                                                     in
                                                                    FStar_Util.print2
                                                                    "Generated uvar %s with attribute %s\n"
                                                                    uu____4739
                                                                    uu____4741))
                                                      else ());
                                                     (let subst1 =
                                                        FStar_List.map2
                                                          (fun b1  ->
                                                             fun t  ->
                                                               let uu____4778
                                                                 =
                                                                 let uu____4785
                                                                   =
                                                                   FStar_All.pipe_right
                                                                    b1
                                                                    FStar_Pervasives_Native.fst
                                                                    in
                                                                 (uu____4785,
                                                                   t)
                                                                  in
                                                               FStar_Syntax_Syntax.NT
                                                                 uu____4778)
                                                          (a_b :: b_b ::
                                                          rest_bs) (t1 :: t2
                                                          :: rest_bs_uvars)
                                                         in
                                                      let f_guard =
                                                        let f_sort_is =
                                                          let uu____4814 =
                                                            let uu____4817 =
                                                              let uu____4818
                                                                =
                                                                let uu____4819
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                   in
                                                                uu____4819.FStar_Syntax_Syntax.sort
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4818
                                                               in
                                                            let uu____4828 =
                                                              FStar_Syntax_Util.is_layered
                                                                m_ed
                                                               in
                                                            effect_args_from_repr
                                                              uu____4817
                                                              uu____4828 r1
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____4814
                                                            (FStar_List.map
                                                               (FStar_Syntax_Subst.subst
                                                                  subst1))
                                                           in
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun f_i1  ->
                                                                 (let uu____4853
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook")
                                                                     in
                                                                  if
                                                                    uu____4853
                                                                  then
                                                                    let uu____4858
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1  in
                                                                    let uu____4860
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    f_i1  in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____4858
                                                                    uu____4860
                                                                  else ());
                                                                 (let uu____4865
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    f_i1  in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4865))
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is1 f_sort_is
                                                         in
                                                      let g_guard =
                                                        let x_a =
                                                          match b with
                                                          | FStar_Pervasives_Native.None
                                                               ->
                                                              FStar_Syntax_Syntax.null_binder
                                                                ct1.FStar_Syntax_Syntax.result_typ
                                                          | FStar_Pervasives_Native.Some
                                                              x ->
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                           in
                                                        let g_sort_is =
                                                          let uu____4884 =
                                                            let uu____4885 =
                                                              let uu____4888
                                                                =
                                                                let uu____4889
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst
                                                                   in
                                                                uu____4889.FStar_Syntax_Syntax.sort
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4888
                                                               in
                                                            uu____4885.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____4884
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_arrow
                                                              (bs,c) ->
                                                              let uu____4922
                                                                =
                                                                FStar_Syntax_Subst.open_comp
                                                                  bs c
                                                                 in
                                                              (match uu____4922
                                                               with
                                                               | (bs1,c1) ->
                                                                   let bs_subst
                                                                    =
                                                                    let uu____4932
                                                                    =
                                                                    let uu____4939
                                                                    =
                                                                    let uu____4940
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4940
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4961
                                                                    =
                                                                    let uu____4964
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4964
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4939,
                                                                    uu____4961)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4932
                                                                     in
                                                                   let c2 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1  in
                                                                   let uu____4978
                                                                    =
                                                                    let uu____4981
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                    let uu____4982
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                    effect_args_from_repr
                                                                    uu____4981
                                                                    uu____4982
                                                                    r1  in
                                                                   FStar_All.pipe_right
                                                                    uu____4978
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1)))
                                                          | uu____4988 ->
                                                              failwith
                                                                "imspossible: mk_indexed_bind"
                                                           in
                                                        let env_g =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env [x_a]
                                                           in
                                                        let uu____5005 =
                                                          FStar_List.fold_left2
                                                            (fun g  ->
                                                               fun i1  ->
                                                                 fun g_i1  ->
                                                                   (let uu____5023
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook")
                                                                     in
                                                                    if
                                                                    uu____5023
                                                                    then
                                                                    let uu____5028
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1  in
                                                                    let uu____5030
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    g_i1  in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____5028
                                                                    uu____5030
                                                                    else ());
                                                                   (let uu____5035
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____5035))
                                                            FStar_TypeChecker_Env.trivial_guard
                                                            is2 g_sort_is
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5005
                                                          (FStar_TypeChecker_Env.close_guard
                                                             env [x_a])
                                                         in
                                                      let bind_ct =
                                                        let uu____5049 =
                                                          FStar_All.pipe_right
                                                            bind_c
                                                            (FStar_Syntax_Subst.subst_comp
                                                               subst1)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5049
                                                          FStar_Syntax_Util.comp_to_comp_typ
                                                         in
                                                      let fml =
                                                        let uu____5051 =
                                                          let uu____5056 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____5057 =
                                                            let uu____5058 =
                                                              FStar_List.hd
                                                                bind_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____5058
                                                             in
                                                          (uu____5056,
                                                            uu____5057)
                                                           in
                                                        match uu____5051 with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              bind_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let is =
                                                        let uu____5084 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                           in
                                                        let uu____5085 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed
                                                           in
                                                        effect_args_from_repr
                                                          uu____5084
                                                          uu____5085 r1
                                                         in
                                                      let c =
                                                        let uu____5088 =
                                                          let uu____5089 =
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              is
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              =
                                                              (ct2.FStar_Syntax_Syntax.comp_univs);
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              (p_ed.FStar_Syntax_Syntax.mname);
                                                            FStar_Syntax_Syntax.result_typ
                                                              = t2;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____5089;
                                                            FStar_Syntax_Syntax.flags
                                                              = flags
                                                          }  in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____5088
                                                         in
                                                      (let uu____5109 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env)
                                                           (FStar_Options.Other
                                                              "LayeredEffects")
                                                          in
                                                       if uu____5109
                                                       then
                                                         let uu____5114 =
                                                           FStar_Syntax_Print.comp_to_string
                                                             c
                                                            in
                                                         FStar_Util.print1
                                                           "} c after bind: %s\n"
                                                           uu____5114
                                                       else ());
                                                      (let guard =
                                                         let uu____5120 =
                                                           let uu____5123 =
                                                             let uu____5126 =
                                                               let uu____5129
                                                                 =
                                                                 let uu____5132
                                                                   =
                                                                   FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStar_TypeChecker_Common.NonTrivial
                                                                    fml)
                                                                    in
                                                                 [uu____5132]
                                                                  in
                                                               g_guard ::
                                                                 uu____5129
                                                                in
                                                             f_guard ::
                                                               uu____5126
                                                              in
                                                           g_uvars ::
                                                             uu____5123
                                                            in
                                                         FStar_TypeChecker_Env.conj_guards
                                                           uu____5120
                                                          in
                                                       (let uu____5134 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "ResolveImplicitsHook")
                                                           in
                                                        if uu____5134
                                                        then
                                                          let uu____5139 =
                                                            let uu____5141 =
                                                              FStar_TypeChecker_Env.get_range
                                                                env
                                                               in
                                                            FStar_Range.string_of_range
                                                              uu____5141
                                                             in
                                                          let uu____5142 =
                                                            FStar_TypeChecker_Rel.guard_to_string
                                                              env guard
                                                             in
                                                          FStar_Util.print2
                                                            "///////////////////////////////EndBind at %s/////////////////////\nguard = %s\n"
                                                            uu____5139
                                                            uu____5142
                                                        else ());
                                                       (c, guard))))))))))
  
let (mk_wp_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.comp_typ ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          FStar_Syntax_Syntax.comp_typ ->
            FStar_Syntax_Syntax.cflag Prims.list ->
              FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun m  ->
      fun ct1  ->
        fun b  ->
          fun ct2  ->
            fun flags  ->
              fun r1  ->
                let uu____5191 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____5217 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____5217 with
                  | (a,kwp) ->
                      let uu____5248 = destruct_wp_comp ct1  in
                      let uu____5255 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____5248, uu____5255)
                   in
                match uu____5191 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5308 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5308]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5328 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5328]
                       in
                    let mk_lam wp =
                      FStar_Syntax_Util.abs bs wp
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.mk_residual_comp
                              FStar_Parser_Const.effect_Tot_lid
                              FStar_Pervasives_Native.None
                              [FStar_Syntax_Syntax.TOTAL]))
                       in
                    let r11 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_range r1))
                        FStar_Pervasives_Native.None r1
                       in
                    let wp_args =
                      let uu____5375 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5384 =
                        let uu____5395 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5404 =
                          let uu____5415 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5424 =
                            let uu____5435 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5444 =
                              let uu____5455 =
                                let uu____5464 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5464  in
                              [uu____5455]  in
                            uu____5435 :: uu____5444  in
                          uu____5415 :: uu____5424  in
                        uu____5395 :: uu____5404  in
                      uu____5375 :: uu____5384  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5517 =
                        let uu____5522 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5522 wp_args  in
                      uu____5517 FStar_Pervasives_Native.None
                        t2.FStar_Syntax_Syntax.pos
                       in
                    mk_comp md u_t2 t2 wp flags
  
let (mk_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.cflag Prims.list ->
            FStar_Range.range ->
              (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun b  ->
        fun c2  ->
          fun flags  ->
            fun r1  ->
              let uu____5570 =
                let uu____5575 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5576 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5575, uu____5576)  in
              match uu____5570 with
              | (ct1,ct2) ->
                  let uu____5583 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5583 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5634 = lift_comps env c1 c2 b true  in
                       (match uu____5634 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5652 =
                              let uu____5657 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5658 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5657, uu____5658)  in
                            (match uu____5652 with
                             | (ct11,ct21) ->
                                 let uu____5665 =
                                   let uu____5670 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5670
                                   then
                                     let bind_t =
                                       let uu____5678 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5678
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5681 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5681,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5665 with
                                  | (c,g_bind) ->
                                      let uu____5688 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5688)))))
  
let (bind_pure_wp_with :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.cflag Prims.list ->
          (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun wp1  ->
      fun c  ->
        fun flags  ->
          let r = FStar_TypeChecker_Env.get_range env  in
          let pure_c =
            let uu____5724 =
              let uu____5725 =
                let uu____5736 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5736]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5725;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5724  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5781 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5787  ->
              match uu___1_5787 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5790 -> false))
       in
    if uu____5781
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5802  ->
              match uu___2_5802 with
              | FStar_Syntax_Syntax.TOTAL  ->
                  [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | FStar_Syntax_Syntax.RETURN  ->
                  [FStar_Syntax_Syntax.PARTIAL_RETURN;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | f -> [f]))
  
let (weaken_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun formula  ->
        let uu____5830 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5830
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5841 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5841  in
           let pure_assume_wp1 =
             let uu____5846 = FStar_TypeChecker_Env.get_range env  in
             let uu____5847 =
               let uu____5852 =
                 let uu____5853 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5853]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5852  in
             uu____5847 FStar_Pervasives_Native.None uu____5846  in
           let uu____5886 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5886)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5914 =
          let uu____5915 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5915 with
          | (c,g_c) ->
              let uu____5926 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5926
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5940 = weaken_comp env c f1  in
                     (match uu____5940 with
                      | (c1,g_w) ->
                          let uu____5951 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5951)))
           in
        let uu____5952 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5952 weaken
  
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflag Prims.list ->
            (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun reason  ->
      fun c  ->
        fun f  ->
          fun flags  ->
            if env.FStar_TypeChecker_Env.lax
            then (c, FStar_TypeChecker_Env.trivial_guard)
            else
              (let r = FStar_TypeChecker_Env.get_range env  in
               let pure_assert_wp =
                 let uu____6009 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____6009  in
               let pure_assert_wp1 =
                 let uu____6014 =
                   let uu____6019 =
                     let uu____6020 =
                       let uu____6029 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____6029
                        in
                     [uu____6020]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____6019
                    in
                 uu____6014 FStar_Pervasives_Native.None r  in
               bind_pure_wp_with env pure_assert_wp1 c flags)
  
let (strengthen_precondition :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.lcomp ->
          FStar_TypeChecker_Common.guard_t ->
            (FStar_TypeChecker_Common.lcomp *
              FStar_TypeChecker_Common.guard_t))
  =
  fun reason  ->
    fun env  ->
      fun e_for_debugging_only  ->
        fun lc  ->
          fun g0  ->
            let uu____6099 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____6099
            then (lc, g0)
            else
              (let flags =
                 let uu____6111 =
                   let uu____6119 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____6119
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____6111 with
                 | (maybe_trivial_post,flags) ->
                     let uu____6149 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_6157  ->
                               match uu___3_6157 with
                               | FStar_Syntax_Syntax.RETURN  ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.SOMETRIVIAL  when
                                   Prims.op_Negation maybe_trivial_post ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION 
                                   when Prims.op_Negation maybe_trivial_post
                                   ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                   [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                               | uu____6160 -> []))
                        in
                     FStar_List.append flags uu____6149
                  in
               let strengthen uu____6170 =
                 let uu____6171 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____6171 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____6190 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____6190 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6197 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6197
                              then
                                let uu____6201 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6203 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6201 uu____6203
                              else ());
                             (let uu____6208 =
                                strengthen_comp env reason c f flags  in
                              match uu____6208 with
                              | (c1,g_s) ->
                                  let uu____6219 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6219))))
                  in
               let uu____6220 =
                 let uu____6221 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6221
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6220,
                 (let uu___727_6223 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred_to_tac =
                      (uu___727_6223.FStar_TypeChecker_Common.deferred_to_tac);
                    FStar_TypeChecker_Common.deferred =
                      (uu___727_6223.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___727_6223.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___727_6223.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6232  ->
            match uu___4_6232 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6236 -> false) lc.FStar_TypeChecker_Common.cflags)
  
let (maybe_add_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun uopt  ->
      fun lc  ->
        fun e  ->
          let uu____6265 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6265
          then e
          else
            (let uu____6272 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6275 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6275)
                in
             if uu____6272
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u -> u
                 | FStar_Pervasives_Native.None  ->
                     env.FStar_TypeChecker_Env.universe_of env
                       lc.FStar_TypeChecker_Common.res_typ
                  in
               FStar_Syntax_Util.mk_with_type u
                 lc.FStar_TypeChecker_Common.res_typ e
             else e)
  
let (maybe_capture_unit_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun t  ->
      fun x  ->
        fun c  ->
          let t1 =
            FStar_TypeChecker_Normalize.normalize_refinement
              FStar_TypeChecker_Normalize.whnf_steps env t
             in
          match t1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (b,phi) ->
              let is_unit1 =
                match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.unit_lid
                | uu____6345 -> false  in
              if is_unit1
              then
                let uu____6352 =
                  let uu____6354 =
                    let uu____6355 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6355
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6354
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6352
                 then
                   let uu____6364 = FStar_Syntax_Subst.open_term_bv b phi  in
                   match uu____6364 with
                   | (b1,phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1
                          in
                       weaken_comp env c phi2
                 else
                   (let uu____6380 = close_wp_comp env [x] c  in
                    (uu____6380, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6383 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
let (bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Common.lcomp ->
          lcomp_with_binder -> FStar_TypeChecker_Common.lcomp)
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____6411  ->
            match uu____6411 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____6431 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6431 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6444 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6444
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6454 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6454
                       then
                         let uu____6459 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6459
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6466 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6466
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6475 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6475
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6482 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6482
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6498 =
                  let uu____6499 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6499
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6507 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6507, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6510 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6510 with
                     | (c1,g_c1) ->
                         let uu____6521 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6521 with
                          | (c2,g_c2) ->
                              let trivial_guard1 =
                                let uu____6533 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6536 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6536
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6533
                                 in
                              (debug1
                                 (fun uu____6562  ->
                                    let uu____6563 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6565 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6570 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6563 uu____6565 uu____6570);
                               (let aux uu____6588 =
                                  let uu____6589 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6589
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6620
                                        ->
                                        let uu____6621 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6621
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6653 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6653
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6700 =
                                  let aux_with_trivial_guard uu____6730 =
                                    let uu____6731 = aux ()  in
                                    match uu____6731 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard1, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6789 =
                                    let uu____6791 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6791  in
                                  if uu____6789
                                  then
                                    let uu____6807 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6807
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard1,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6834 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6834))
                                  else
                                    (let uu____6851 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6851
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___830_6882 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___830_6882.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___830_6882.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         maybe_capture_unit_refinement env
                                           x1.FStar_Syntax_Syntax.sort x1 c
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____6913 =
                                             let uu____6918 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____6918
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6913 with
                                            | (c21,g_close) ->
                                                let uu____6939 =
                                                  let uu____6947 =
                                                    let uu____6948 =
                                                      let uu____6951 =
                                                        let uu____6954 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____6954; g_close]
                                                         in
                                                      g_c1 :: uu____6951  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6948
                                                     in
                                                  (c21, uu____6947, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____6939)
                                       | (uu____6967,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____6979 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6979 with
                                            | (c21,g_close) ->
                                                let uu____7002 =
                                                  let uu____7010 =
                                                    let uu____7011 =
                                                      let uu____7014 =
                                                        let uu____7017 =
                                                          let uu____7018 =
                                                            let uu____7019 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____7019]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____7018
                                                            g_c2
                                                           in
                                                        [uu____7017; g_close]
                                                         in
                                                      g_c1 :: uu____7014  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____7011
                                                     in
                                                  (c21, uu____7010,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____7002)
                                       | (uu____7048,uu____7049) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____7064 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____7064
                                        then
                                          let uu____7079 =
                                            let uu____7087 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____7087, trivial_guard1,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____7079
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____7100 = try_simplify ()  in
                                match uu____7100 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug1
                                       (fun uu____7135  ->
                                          let uu____7136 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____7136);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____7152  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____7183 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____7183 with
                                        | (c,g_bind) ->
                                            let uu____7194 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____7194)
                                         in
                                      let mk_seq c11 b1 c21 =
                                        let c12 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c11
                                           in
                                        let c22 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c21
                                           in
                                        let uu____7221 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7221 with
                                        | (m,uu____7233,lift2) ->
                                            let uu____7235 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7235 with
                                             | (c23,g2) ->
                                                 let uu____7246 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7246 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7262 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7262
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7272 =
                                                          let uu____7277 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____7278 =
                                                            let uu____7279 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____7288 =
                                                              let uu____7299
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____7299]
                                                               in
                                                            uu____7279 ::
                                                              uu____7288
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7277
                                                            uu____7278
                                                           in
                                                        uu____7272
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____7332 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7332 with
                                                       | (c,g_s) ->
                                                           let uu____7347 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7347))))
                                         in
                                      let uu____7348 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7364 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7364, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7348 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7380 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7380
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7389 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7389
                                             then
                                               (debug1
                                                  (fun uu____7403  ->
                                                     let uu____7404 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7406 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7404 uu____7406);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____7413 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7413
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7418 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7421 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7421)
                                                   in
                                                if uu____7418
                                                then
                                                  let e1' =
                                                    let uu____7446 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7446
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____7458  ->
                                                        let uu____7459 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7461 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7459
                                                          uu____7461);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____7476  ->
                                                        let uu____7477 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7479 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7477
                                                          uu____7479);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7486 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7486
                                                       in
                                                    let uu____7487 =
                                                      let uu____7492 =
                                                        let uu____7493 =
                                                          let uu____7494 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7494]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7493
                                                         in
                                                      weaken_comp uu____7492
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7487 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7520 =
                                                            let uu____7521 =
                                                              let uu____7522
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7522]
                                                               in
                                                            let uu____7541 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7521
                                                              uu____7541
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7520
                                                           in
                                                        let uu____7542 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7542
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7553 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7553))))))
                                          else
                                            mk_bind1 c1 b c2 trivial_guard1))))))
                   in
                FStar_TypeChecker_Common.mk_lcomp joined_eff
                  lc21.FStar_TypeChecker_Common.res_typ bind_flags bind_it
  
let (weaken_guard :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let g = FStar_Syntax_Util.mk_imp f1 f2  in
          FStar_TypeChecker_Common.NonTrivial g
      | uu____7570 -> g2
  
let (maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let should_return1 =
          (((Prims.op_Negation env.FStar_TypeChecker_Env.lax) &&
              (FStar_TypeChecker_Env.lid_exists env
                 FStar_Parser_Const.effect_GTot_lid))
             && (should_return env (FStar_Pervasives_Native.Some e) lc))
            &&
            (let uu____7594 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7594)
           in
        let flags =
          if should_return1
          then
            let uu____7602 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7602
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____7620 =
          let uu____7621 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7621 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7634 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7634
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7642 =
                  let uu____7644 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7644  in
                (if uu____7642
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___955_7653 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___955_7653.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___955_7653.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___955_7653.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7654 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7654, g_c)
                 else
                   (let uu____7657 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7657, g_c)))
              else
                (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c
                    in
                 let t = c1.FStar_Syntax_Syntax.result_typ  in
                 let c2 = FStar_Syntax_Syntax.mk_Comp c1  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (t.FStar_Syntax_Syntax.pos)) t
                    in
                 let xexp = FStar_Syntax_Syntax.bv_to_name x  in
                 let ret1 =
                   let uu____7668 =
                     let uu____7669 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7669
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7668
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____7672 =
                   let uu____7677 =
                     let uu____7678 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7678
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7677  in
                 match uu____7672 with
                 | (bind_c,g_bind) ->
                     let uu____7687 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7688 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7687, uu____7688))
           in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_TypeChecker_Common.mk_lcomp
            lc.FStar_TypeChecker_Common.eff_name
            lc.FStar_TypeChecker_Common.res_typ flags refine1
  
let (maybe_return_e2_and_bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Common.lcomp ->
          FStar_Syntax_Syntax.term ->
            lcomp_with_binder -> FStar_TypeChecker_Common.lcomp)
  =
  fun r  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun e2  ->
            fun uu____7724  ->
              match uu____7724 with
              | (x,lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_TypeChecker_Common.eff_name
                       in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_TypeChecker_Common.eff_name
                       in
                    let uu____7736 =
                      ((let uu____7740 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7740) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7736
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7758 =
        let uu____7759 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7759  in
      FStar_Syntax_Syntax.fvar uu____7758 FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
  
let (mk_layered_conjunction :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.comp_typ ->
              FStar_Syntax_Syntax.comp_typ ->
                FStar_Range.range ->
                  (FStar_Syntax_Syntax.comp *
                    FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun p  ->
            fun ct1  ->
              fun ct2  ->
                fun r  ->
                  let uu____7809 =
                    let uu____7814 =
                      let uu____7815 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7815 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7814 [u_a]
                     in
                  match uu____7809 with
                  | (uu____7826,conjunction) ->
                      let uu____7828 =
                        let uu____7837 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7852 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7837, uu____7852)  in
                      (match uu____7828 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7898 =
                               let uu____7900 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7900 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7898)
                              in
                           let uu____7904 =
                             let uu____7949 =
                               let uu____7950 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7950.FStar_Syntax_Syntax.n  in
                             match uu____7949 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7999) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____8031 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____8031 with
                                  | (a_b::bs1,body1) ->
                                      let uu____8103 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____8103 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8251 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8251)))
                             | uu____8284 ->
                                 let uu____8285 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8285 r
                              in
                           (match uu____7904 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8410 =
                                  let uu____8417 =
                                    let uu____8418 =
                                      let uu____8419 =
                                        let uu____8426 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8426, a)  in
                                      FStar_Syntax_Syntax.NT uu____8419  in
                                    [uu____8418]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8417
                                    (fun b  ->
                                       let uu____8442 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8444 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8446 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8442 uu____8444 uu____8446) r
                                   in
                                (match uu____8410 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8484 =
                                                let uu____8491 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8491, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8484) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8530 =
                                           let uu____8531 =
                                             let uu____8534 =
                                               let uu____8535 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8535.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8534
                                              in
                                           uu____8531.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8530 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8546,uu____8547::is) ->
                                             let uu____8589 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8589
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8622 ->
                                             let uu____8623 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8623 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8639 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8639)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8644 =
                                           let uu____8645 =
                                             let uu____8648 =
                                               let uu____8649 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8649.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8648
                                              in
                                           uu____8645.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8644 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8660,uu____8661::is) ->
                                             let uu____8703 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8703
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8736 ->
                                             let uu____8737 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8737 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8753 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8753)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8758 =
                                         let uu____8759 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8759.FStar_Syntax_Syntax.n  in
                                       match uu____8758 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8764,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8819 ->
                                           let uu____8820 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8820 r
                                        in
                                     let uu____8829 =
                                       let uu____8830 =
                                         let uu____8831 =
                                           FStar_All.pipe_right is
                                             (FStar_List.map
                                                FStar_Syntax_Syntax.as_arg)
                                            in
                                         {
                                           FStar_Syntax_Syntax.comp_univs =
                                             [u_a];
                                           FStar_Syntax_Syntax.effect_name =
                                             (ed.FStar_Syntax_Syntax.mname);
                                           FStar_Syntax_Syntax.result_typ = a;
                                           FStar_Syntax_Syntax.effect_args =
                                             uu____8831;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8830
                                        in
                                     let uu____8854 =
                                       let uu____8855 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8855 g_guard
                                        in
                                     (uu____8829, uu____8854))))
  
let (mk_non_layered_conjunction :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.comp_typ ->
              FStar_Syntax_Syntax.comp_typ ->
                FStar_Range.range ->
                  (FStar_Syntax_Syntax.comp *
                    FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun p  ->
            fun ct1  ->
              fun ct2  ->
                fun uu____8900  ->
                  let if_then_else1 =
                    let uu____8906 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8906 FStar_Util.must  in
                  let uu____8913 = destruct_wp_comp ct1  in
                  match uu____8913 with
                  | (uu____8924,uu____8925,wp_t) ->
                      let uu____8927 = destruct_wp_comp ct2  in
                      (match uu____8927 with
                       | (uu____8938,uu____8939,wp_e) ->
                           let wp =
                             let uu____8944 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8945 =
                               let uu____8950 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____8951 =
                                 let uu____8952 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8961 =
                                   let uu____8972 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8981 =
                                     let uu____8992 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____9001 =
                                       let uu____9012 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____9012]  in
                                     uu____8992 :: uu____9001  in
                                   uu____8972 :: uu____8981  in
                                 uu____8952 :: uu____8961  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8950
                                 uu____8951
                                in
                             uu____8945 FStar_Pervasives_Native.None
                               uu____8944
                              in
                           let uu____9061 = mk_comp ed u_a a wp []  in
                           (uu____9061, FStar_TypeChecker_Env.trivial_guard))
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ * FStar_Ident.lident *
        FStar_Syntax_Syntax.cflag Prims.list *
        (Prims.bool -> FStar_TypeChecker_Common.lcomp)) Prims.list ->
        FStar_Syntax_Syntax.bv -> FStar_TypeChecker_Common.lcomp)
  =
  fun env0  ->
    fun res_t  ->
      fun lcases  ->
        fun scrutinee  ->
          let env =
            let uu____9115 =
              let uu____9116 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____9116]  in
            FStar_TypeChecker_Env.push_binders env0 uu____9115  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____9163  ->
                   match uu____9163 with
                   | (uu____9177,eff_label,uu____9179,uu____9180) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____9193 =
            let uu____9201 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9239  ->
                      match uu____9239 with
                      | (uu____9254,uu____9255,flags,uu____9257) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9274  ->
                                  match uu___5_9274 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9277 -> false))))
               in
            if uu____9201
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____9193 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9314 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9316 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9316
                then
                  let uu____9323 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9323, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let default_case =
                     let post_k =
                       let uu____9330 =
                         let uu____9339 =
                           FStar_Syntax_Syntax.null_binder res_t  in
                         [uu____9339]  in
                       let uu____9358 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9330 uu____9358  in
                     let kwp =
                       let uu____9364 =
                         let uu____9373 =
                           FStar_Syntax_Syntax.null_binder post_k  in
                         [uu____9373]  in
                       let uu____9392 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9364 uu____9392  in
                     let post =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None post_k
                        in
                     let wp =
                       let uu____9399 =
                         let uu____9400 = FStar_Syntax_Syntax.mk_binder post
                            in
                         [uu____9400]  in
                       let uu____9419 =
                         let uu____9422 =
                           let uu____9429 =
                             FStar_TypeChecker_Env.get_range env  in
                           label FStar_TypeChecker_Err.exhaustiveness_check
                             uu____9429
                            in
                         let uu____9430 =
                           fvar_const env FStar_Parser_Const.false_lid  in
                         FStar_All.pipe_left uu____9422 uu____9430  in
                       FStar_Syntax_Util.abs uu____9399 uu____9419
                         (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Util.mk_residual_comp
                               FStar_Parser_Const.effect_Tot_lid
                               FStar_Pervasives_Native.None
                               [FStar_Syntax_Syntax.TOTAL]))
                        in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         FStar_Parser_Const.effect_PURE_lid
                        in
                     mk_comp md u_res_t res_t wp []  in
                   let maybe_return eff_label_then cthen =
                     let uu____9454 =
                       should_not_inline_whole_match ||
                         (let uu____9457 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9457)
                        in
                     if uu____9454 then cthen true else cthen false  in
                   let branch_conditions =
                     let uu____9469 =
                       let uu____9482 =
                         let uu____9487 =
                           let uu____9498 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9542  ->
                                     match uu____9542 with
                                     | (g,uu____9557,uu____9558,uu____9559)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9498
                             (FStar_List.fold_left
                                (fun uu____9603  ->
                                   fun g  ->
                                     match uu____9603 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9644 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9644
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9487
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9482
                         (FStar_List.splitAt (FStar_List.length lcases))
                        in
                     FStar_All.pipe_right uu____9469
                       FStar_Pervasives_Native.fst
                      in
                   let uu____9745 =
                     FStar_List.fold_right2
                       (fun uu____9808  ->
                          fun bcond  ->
                            fun uu____9810  ->
                              match (uu____9808, uu____9810) with
                              | ((g,eff_label,uu____9870,cthen),(uu____9872,celse,g_comp))
                                  ->
                                  let uu____9919 =
                                    let uu____9924 =
                                      maybe_return eff_label cthen  in
                                    FStar_TypeChecker_Common.lcomp_comp
                                      uu____9924
                                     in
                                  (match uu____9919 with
                                   | (cthen1,gthen) ->
                                       let gthen1 =
                                         let uu____9936 =
                                           FStar_Syntax_Util.mk_conj bcond g
                                            in
                                         FStar_TypeChecker_Common.weaken_guard_formula
                                           gthen uu____9936
                                          in
                                       let uu____9937 =
                                         let uu____9948 =
                                           lift_comps_sep_guards env cthen1
                                             celse
                                             FStar_Pervasives_Native.None
                                             false
                                            in
                                         match uu____9948 with
                                         | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                             ->
                                             let md =
                                               FStar_TypeChecker_Env.get_effect_decl
                                                 env m
                                                in
                                             let uu____9976 =
                                               FStar_All.pipe_right cthen2
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             let uu____9977 =
                                               FStar_All.pipe_right celse1
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             (md, uu____9976, uu____9977,
                                               g_lift_then, g_lift_else)
                                          in
                                       (match uu____9937 with
                                        | (md,ct_then,ct_else,g_lift_then,g_lift_else)
                                            ->
                                            let fn =
                                              let uu____10028 =
                                                FStar_All.pipe_right md
                                                  FStar_Syntax_Util.is_layered
                                                 in
                                              if uu____10028
                                              then mk_layered_conjunction
                                              else mk_non_layered_conjunction
                                               in
                                            let g_lift_then1 =
                                              let uu____10063 =
                                                FStar_Syntax_Util.mk_conj
                                                  bcond g
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_then uu____10063
                                               in
                                            let g_lift_else1 =
                                              let uu____10065 =
                                                let uu____10066 =
                                                  FStar_Syntax_Util.mk_neg g
                                                   in
                                                FStar_Syntax_Util.mk_conj
                                                  bcond uu____10066
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_else uu____10065
                                               in
                                            let g_lift =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_lift_then1 g_lift_else1
                                               in
                                            let uu____10070 =
                                              let uu____10075 =
                                                FStar_TypeChecker_Env.get_range
                                                  env
                                                 in
                                              fn env md u_res_t res_t g
                                                ct_then ct_else uu____10075
                                               in
                                            (match uu____10070 with
                                             | (c,g_conjunction) ->
                                                 let uu____10086 =
                                                   FStar_TypeChecker_Env.conj_guards
                                                     [g_comp;
                                                     gthen1;
                                                     g_lift;
                                                     g_conjunction]
                                                    in
                                                 ((FStar_Pervasives_Native.Some
                                                     md), c, uu____10086)))))
                       lcases branch_conditions
                       (FStar_Pervasives_Native.None, default_case,
                         FStar_TypeChecker_Env.trivial_guard)
                      in
                   match uu____9745 with
                   | (md,comp,g_comp) ->
                       let g_comp1 =
                         let uu____10103 =
                           let uu____10104 =
                             FStar_All.pipe_right scrutinee
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____10104]  in
                         FStar_TypeChecker_Env.close_guard env0 uu____10103
                           g_comp
                          in
                       (match lcases with
                        | [] -> (comp, g_comp1)
                        | uu____10147::[] -> (comp, g_comp1)
                        | uu____10190 ->
                            let uu____10207 =
                              let uu____10209 =
                                FStar_All.pipe_right md FStar_Util.must  in
                              FStar_All.pipe_right uu____10209
                                FStar_Syntax_Util.is_layered
                               in
                            if uu____10207
                            then (comp, g_comp1)
                            else
                              (let comp1 =
                                 FStar_TypeChecker_Env.comp_to_comp_typ env
                                   comp
                                  in
                               let md1 =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   comp1.FStar_Syntax_Syntax.effect_name
                                  in
                               let uu____10222 = destruct_wp_comp comp1  in
                               match uu____10222 with
                               | (uu____10233,uu____10234,wp) ->
                                   let ite_wp =
                                     let uu____10237 =
                                       FStar_All.pipe_right md1
                                         FStar_Syntax_Util.get_wp_ite_combinator
                                        in
                                     FStar_All.pipe_right uu____10237
                                       FStar_Util.must
                                      in
                                   let wp1 =
                                     let uu____10247 =
                                       let uu____10252 =
                                         FStar_TypeChecker_Env.inst_effect_fun_with
                                           [u_res_t] env md1 ite_wp
                                          in
                                       let uu____10253 =
                                         let uu____10254 =
                                           FStar_Syntax_Syntax.as_arg res_t
                                            in
                                         let uu____10263 =
                                           let uu____10274 =
                                             FStar_Syntax_Syntax.as_arg wp
                                              in
                                           [uu____10274]  in
                                         uu____10254 :: uu____10263  in
                                       FStar_Syntax_Syntax.mk_Tm_app
                                         uu____10252 uu____10253
                                        in
                                     uu____10247 FStar_Pervasives_Native.None
                                       wp.FStar_Syntax_Syntax.pos
                                      in
                                   let uu____10307 =
                                     mk_comp md1 u_res_t res_t wp1
                                       bind_cases_flags
                                      in
                                   (uu____10307, g_comp1))))
                 in
              FStar_TypeChecker_Common.mk_lcomp eff res_t bind_cases_flags
                bind_cases
  
let (check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____10342 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____10342 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10358 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____10364 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____10358 uu____10364
              else
                (let uu____10373 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____10379 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____10373 uu____10379)
          | FStar_Pervasives_Native.Some g -> (e, c', g)
  
let (universe_of_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u_res  ->
      fun c  ->
        let c_lid =
          let uu____10404 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____10404
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____10407 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____10407
        then u_res
        else
          (let is_total =
             let uu____10414 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____10414
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____10425 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____10425 with
              | FStar_Pervasives_Native.None  ->
                  let uu____10428 =
                    let uu____10434 =
                      let uu____10436 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____10436
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____10434)
                     in
                  FStar_Errors.raise_error uu____10428
                    c.FStar_Syntax_Syntax.pos
              | FStar_Pervasives_Native.Some tm ->
                  env.FStar_TypeChecker_Env.universe_of env tm))
  
let (check_trivial_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp_typ * FStar_Syntax_Syntax.formula *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      let ct =
        FStar_All.pipe_right c
          (FStar_TypeChecker_Env.unfold_effect_abbrev env)
         in
      let md =
        FStar_TypeChecker_Env.get_effect_decl env
          ct.FStar_Syntax_Syntax.effect_name
         in
      let uu____10460 = destruct_wp_comp ct  in
      match uu____10460 with
      | (u_t,t,wp) ->
          let vc =
            let uu____10479 = FStar_TypeChecker_Env.get_range env  in
            let uu____10480 =
              let uu____10485 =
                let uu____10486 =
                  let uu____10487 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____10487 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____10486
                 in
              let uu____10494 =
                let uu____10495 = FStar_Syntax_Syntax.as_arg t  in
                let uu____10504 =
                  let uu____10515 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____10515]  in
                uu____10495 :: uu____10504  in
              FStar_Syntax_Syntax.mk_Tm_app uu____10485 uu____10494  in
            uu____10480 FStar_Pervasives_Native.None uu____10479  in
          let uu____10548 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____10548)
  
let (coerce_with :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.universes ->
              FStar_Syntax_Syntax.args ->
                (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp) ->
                  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun ty  ->
          fun f  ->
            fun us  ->
              fun eargs  ->
                fun mkcomp  ->
                  let uu____10603 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____10603 with
                  | FStar_Pervasives_Native.Some uu____10618 ->
                      ((let uu____10636 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____10636
                        then
                          let uu____10640 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10640
                        else ());
                       (let coercion =
                          let uu____10646 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____10646
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____10653 =
                            let uu____10654 =
                              let uu____10655 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10655
                               in
                            (FStar_Pervasives_Native.None, uu____10654)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10653
                           in
                        let e1 =
                          let uu____10661 =
                            let uu____10666 =
                              let uu____10667 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____10667]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____10666
                             in
                          uu____10661 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____10701 =
                          let uu____10707 =
                            let uu____10709 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10709
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10707)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10701);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____10728 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10746 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10757 -> false 
let rec (check_erased :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> isErased) =
  fun env  ->
    fun t  ->
      let norm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
          FStar_TypeChecker_Env.Primops;
          FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.Iota]
         in
      let t1 = norm' env t  in
      let t2 = FStar_Syntax_Util.unrefine t1  in
      let uu____10781 = FStar_Syntax_Util.head_and_args t2  in
      match uu____10781 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____10826 =
              let uu____10841 =
                let uu____10842 = FStar_Syntax_Subst.compress h1  in
                uu____10842.FStar_Syntax_Syntax.n  in
              (uu____10841, args)  in
            match uu____10826 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____10889,uu____10890) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____10923) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____10944,branches),uu____10946) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____11010 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____11011 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____11011 with
                               | (uu____11012,uu____11013,br_body) ->
                                   let uu____11031 =
                                     let uu____11032 =
                                       let uu____11037 =
                                         let uu____11038 =
                                           let uu____11041 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____11041
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____11038
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____11037  in
                                     FStar_All.pipe_right br_body uu____11032
                                      in
                                   (match uu____11031 with
                                    | No  -> No
                                    | uu____11052 -> Maybe))) No)
            | uu____11053 -> No  in
          r
  
let (maybe_coerce_lc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun exp_t  ->
          let should_coerce =
            (((let uu____11105 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____11105) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11124 =
                 let uu____11125 = FStar_Syntax_Subst.compress t1  in
                 uu____11125.FStar_Syntax_Syntax.n  in
               match uu____11124 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____11130 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11140 =
                 let uu____11141 = FStar_Syntax_Subst.compress t1  in
                 uu____11141.FStar_Syntax_Syntax.n  in
               match uu____11140 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____11146 -> false  in
             let is_type1 t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____11157 =
                 let uu____11158 = FStar_Syntax_Subst.compress t2  in
                 uu____11158.FStar_Syntax_Syntax.n  in
               match uu____11157 with
               | FStar_Syntax_Syntax.Tm_type uu____11162 -> true
               | uu____11164 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____11167 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____11167 with
             | (head1,args) ->
                 ((let uu____11217 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____11217
                   then
                     let uu____11221 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____11223 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____11225 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____11227 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11221 uu____11223 uu____11225 uu____11227
                   else ());
                  (let mk_erased u t =
                     let uu____11245 =
                       let uu____11248 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11248 [u]  in
                     let uu____11249 =
                       let uu____11260 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____11260]  in
                     FStar_Syntax_Util.mk_app uu____11245 uu____11249  in
                   let uu____11285 =
                     let uu____11300 =
                       let uu____11301 = FStar_Syntax_Util.un_uinst head1  in
                       uu____11301.FStar_Syntax_Syntax.n  in
                     (uu____11300, args)  in
                   match uu____11285 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 exp_t)
                       ->
                       let uu____11339 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____11339 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11379 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11379 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11419 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11419 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11459 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11459 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____11480 ->
                       let uu____11495 =
                         let uu____11500 = check_erased env res_typ  in
                         let uu____11501 = check_erased env exp_t  in
                         (uu____11500, uu____11501)  in
                       (match uu____11495 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11510 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____11510 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____11521 =
                                   let uu____11526 =
                                     let uu____11527 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____11527]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____11526
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____11521 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11562 =
                              let uu____11567 =
                                let uu____11568 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____11568]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____11567
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____11562 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____11601 ->
                            (e, lc, FStar_TypeChecker_Env.trivial_guard)))))
  
let (coerce_views :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let rt = lc.FStar_TypeChecker_Common.res_typ  in
        let rt1 = FStar_Syntax_Util.unrefine rt  in
        let uu____11636 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____11636 with
        | (hd1,args) ->
            let uu____11685 =
              let uu____11700 =
                let uu____11701 = FStar_Syntax_Subst.compress hd1  in
                uu____11701.FStar_Syntax_Syntax.n  in
              (uu____11700, args)  in
            (match uu____11685 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11739 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun _11766  -> FStar_Pervasives_Native.Some _11766)
                   uu____11739
             | uu____11767 -> FStar_Pervasives_Native.None)
  
let (weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          (let uu____11820 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____11820
           then
             let uu____11823 = FStar_Syntax_Print.term_to_string e  in
             let uu____11825 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____11827 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11823 uu____11825 uu____11827
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____11837 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____11837 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11862 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____11888 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____11888, false)
             else
               (let uu____11898 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____11898, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____11911) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____11923 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____11923
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1397_11939 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1397_11939.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1397_11939.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1397_11939.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____11946 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____11946 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____11962 =
                      let uu____11963 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____11963 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____11983 =
                            let uu____11985 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____11985 = FStar_Syntax_Util.Equal  in
                          if uu____11983
                          then
                            ((let uu____11992 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____11992
                              then
                                let uu____11996 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____11998 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____11996 uu____11998
                              else ());
                             (let uu____12003 = set_result_typ1 c  in
                              (uu____12003, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____12010 ->
                                   true
                               | uu____12018 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____12027 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____12027
                                  in
                               let lc1 =
                                 let uu____12029 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____12030 =
                                   let uu____12031 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____12031)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____12029 uu____12030
                                  in
                               ((let uu____12035 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12035
                                 then
                                   let uu____12039 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____12041 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____12043 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____12045 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____12039 uu____12041 uu____12043
                                     uu____12045
                                 else ());
                                (let uu____12050 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____12050 with
                                 | (c1,g_lc) ->
                                     let uu____12061 = set_result_typ1 c1  in
                                     let uu____12062 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____12061, uu____12062)))
                             else
                               ((let uu____12066 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12066
                                 then
                                   let uu____12070 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____12072 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____12070 uu____12072
                                 else ());
                                (let uu____12077 = set_result_typ1 c  in
                                 (uu____12077, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1434_12081 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1434_12081.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1434_12081.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1434_12081.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1434_12081.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____12091 =
                      let uu____12092 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____12092
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____12102 =
                           let uu____12103 = FStar_Syntax_Subst.compress f1
                              in
                           uu____12103.FStar_Syntax_Syntax.n  in
                         match uu____12102 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____12110,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____12112;
                                            FStar_Syntax_Syntax.vars =
                                              uu____12113;_},uu____12114)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1450_12140 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1450_12140.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1450_12140.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1450_12140.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____12141 ->
                             let uu____12142 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____12142 with
                              | (c,g_c) ->
                                  ((let uu____12154 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____12154
                                    then
                                      let uu____12158 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____12160 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____12162 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____12164 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____12158 uu____12160 uu____12162
                                        uu____12164
                                    else ());
                                   (let u_t_opt = comp_univ_opt c  in
                                    let x =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (t.FStar_Syntax_Syntax.pos)) t
                                       in
                                    let xexp =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let cret =
                                      return_value env u_t_opt t xexp  in
                                    let guard =
                                      if apply_guard1
                                      then
                                        let uu____12177 =
                                          let uu____12182 =
                                            let uu____12183 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____12183]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____12182
                                           in
                                        uu____12177
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____12210 =
                                      let uu____12215 =
                                        FStar_All.pipe_left
                                          (fun _12236  ->
                                             FStar_Pervasives_Native.Some
                                               _12236)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____12237 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____12238 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____12239 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____12215
                                        uu____12237 e uu____12238 uu____12239
                                       in
                                    match uu____12210 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1468_12247 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1468_12247.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1468_12247.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____12249 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____12249
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____12252 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____12252 with
                                         | (c2,g_lc) ->
                                             ((let uu____12264 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____12264
                                               then
                                                 let uu____12268 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____12268
                                               else ());
                                              (let uu____12273 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____12273))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12282  ->
                              match uu___6_12282 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12285 -> []))
                       in
                    let lc1 =
                      let uu____12287 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____12287 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1484_12289 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1484_12289.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1484_12289.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1484_12289.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1484_12289.FStar_TypeChecker_Common.implicits)
                      }  in
                    (e, lc1, g2)))
  
let (pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t
           in
        let uu____12325 =
          let uu____12328 =
            let uu____12333 =
              let uu____12334 =
                let uu____12343 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____12343  in
              [uu____12334]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____12333  in
          uu____12328 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____12325  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____12366 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____12366
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12385 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____12401 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____12418 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____12418
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____12434)::(ens,uu____12436)::uu____12437 ->
                    let uu____12480 =
                      let uu____12483 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____12483  in
                    let uu____12484 =
                      let uu____12485 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____12485  in
                    (uu____12480, uu____12484)
                | uu____12488 ->
                    let uu____12499 =
                      let uu____12505 =
                        let uu____12507 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____12507
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____12505)
                       in
                    FStar_Errors.raise_error uu____12499
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____12527)::uu____12528 ->
                    let uu____12555 =
                      let uu____12560 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____12560
                       in
                    (match uu____12555 with
                     | (us_r,uu____12592) ->
                         let uu____12593 =
                           let uu____12598 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____12598
                            in
                         (match uu____12593 with
                          | (us_e,uu____12630) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____12633 =
                                  let uu____12634 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12634
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12633
                                  us_r
                                 in
                              let as_ens =
                                let uu____12636 =
                                  let uu____12637 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12637
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12636
                                  us_e
                                 in
                              let req =
                                let uu____12641 =
                                  let uu____12646 =
                                    let uu____12647 =
                                      let uu____12658 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12658]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12647
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____12646
                                   in
                                uu____12641 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____12698 =
                                  let uu____12703 =
                                    let uu____12704 =
                                      let uu____12715 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12715]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12704
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____12703
                                   in
                                uu____12698 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____12752 =
                                let uu____12755 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____12755  in
                              let uu____12756 =
                                let uu____12757 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____12757  in
                              (uu____12752, uu____12756)))
                | uu____12760 -> failwith "Impossible"))
  
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun steps  ->
      fun t  ->
        let tm = FStar_Syntax_Util.mk_reify t  in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            (FStar_List.append
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.Eager_unfolding;
               FStar_TypeChecker_Env.EraseUniverses;
               FStar_TypeChecker_Env.AllowUnboundUniverses;
               FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]
               steps) env tm
           in
        (let uu____12799 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____12799
         then
           let uu____12804 = FStar_Syntax_Print.term_to_string tm  in
           let uu____12806 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12804
             uu____12806
         else ());
        tm'
  
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun steps  ->
      fun head1  ->
        fun arg  ->
          let tm =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
              FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos
             in
          let tm' =
            FStar_TypeChecker_Normalize.normalize
              (FStar_List.append
                 [FStar_TypeChecker_Env.Beta;
                 FStar_TypeChecker_Env.Reify;
                 FStar_TypeChecker_Env.Eager_unfolding;
                 FStar_TypeChecker_Env.EraseUniverses;
                 FStar_TypeChecker_Env.AllowUnboundUniverses;
                 FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]
                 steps) env tm
             in
          (let uu____12865 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____12865
           then
             let uu____12870 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12872 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____12870
               uu____12872
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____12883 =
      let uu____12885 =
        let uu____12886 = FStar_Syntax_Subst.compress t  in
        uu____12886.FStar_Syntax_Syntax.n  in
      match uu____12885 with
      | FStar_Syntax_Syntax.Tm_app uu____12890 -> false
      | uu____12908 -> true  in
    if uu____12883
    then t
    else
      (let uu____12913 = FStar_Syntax_Util.head_and_args t  in
       match uu____12913 with
       | (head1,args) ->
           let uu____12956 =
             let uu____12958 =
               let uu____12959 = FStar_Syntax_Subst.compress head1  in
               uu____12959.FStar_Syntax_Syntax.n  in
             match uu____12958 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____12964 -> false  in
           if uu____12956
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____12996 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
  
let (maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t  in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Env.trivial_guard)
        else
          ((let uu____13043 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____13043
            then
              let uu____13046 = FStar_Syntax_Print.term_to_string e  in
              let uu____13048 = FStar_Syntax_Print.term_to_string t  in
              let uu____13050 =
                let uu____13052 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____13052
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____13046 uu____13048 uu____13050
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____13088 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____13088 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____13122 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____13200  ->
                          match uu____13200 with
                          | (uu____13208,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____13215 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____13215 = FStar_Syntax_Util.Equal)))
                   in
                match uu____13122 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____13334 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____13334 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____13348 =
                      let uu____13354 =
                        let uu____13356 = FStar_Util.string_of_int n_expected
                           in
                        let uu____13358 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____13360 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13356 uu____13358 uu____13360
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13354)
                       in
                    let uu____13364 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____13348 uu____13364
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_13382 =
              match uu___7_13382 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____13425 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____13425 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _13556,uu____13543)
                           when _13556 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____13589,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____13591))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13625 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____13625 with
                            | (v1,uu____13666,g) ->
                                ((let uu____13681 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13681
                                  then
                                    let uu____13684 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13684
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13694 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13694 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____13787 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____13787))))
                       | (uu____13814,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta
                                       tac_or_attr))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let meta_t =
                             match tac_or_attr with
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                 ->
                                 let uu____13853 =
                                   let uu____13860 = FStar_Dyn.mkdyn env  in
                                   (uu____13860, tau)  in
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   uu____13853
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                 attr ->
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_attr attr
                              in
                           let uu____13866 =
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict
                               (FStar_Pervasives_Native.Some meta_t)
                              in
                           (match uu____13866 with
                            | (v1,uu____13907,g) ->
                                ((let uu____13922 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13922
                                  then
                                    let uu____13925 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____13925
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13935 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13935 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____14028 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____14028))))
                       | (uu____14055,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____14103 =
                       let uu____14130 = inst_n_binders t1  in
                       aux [] uu____14130 bs1  in
                     (match uu____14103 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____14202) -> (e, torig, guard)
                           | (uu____14233,[]) when
                               let uu____14264 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____14264 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____14266 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14294 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst1 t2
                                  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   FStar_Pervasives_Native.None
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____14307 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____14319 =
      let uu____14323 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____14323
        (FStar_List.map
           (fun u  ->
              let uu____14335 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____14335 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____14319 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____14363 = FStar_Util.set_is_empty x  in
      if uu____14363
      then []
      else
        (let s =
           let uu____14381 =
             let uu____14384 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____14384  in
           FStar_All.pipe_right uu____14381 FStar_Util.set_elements  in
         (let uu____14400 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____14400
          then
            let uu____14405 =
              let uu____14407 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____14407  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14405
          else ());
         (let r =
            let uu____14416 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____14416  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____14455 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____14455
                     then
                       let uu____14460 =
                         let uu____14462 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____14462
                          in
                       let uu____14466 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____14468 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____14460 uu____14466 uu____14468
                     else ());
                    FStar_Syntax_Unionfind.univ_change u
                      (FStar_Syntax_Syntax.U_name u_name);
                    u_name))
             in
          u_names))
  
let (gather_free_univnames :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun t  ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env  in
      let tm_univnames = FStar_Syntax_Free.univnames t  in
      let univnames1 =
        let uu____14498 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____14498 FStar_Util.set_elements  in
      univnames1
  
let (check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____14537) -> generalized_univ_names
        | (uu____14544,[]) -> explicit_univ_names
        | uu____14551 ->
            let uu____14560 =
              let uu____14566 =
                let uu____14568 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____14568
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____14566)
               in
            FStar_Errors.raise_error uu____14560 t.FStar_Syntax_Syntax.pos
  
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.NoFullNorm;
          FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.DoNotUnfoldPureLets] env t0
         in
      let univnames1 = gather_free_univnames env t  in
      (let uu____14590 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____14590
       then
         let uu____14595 = FStar_Syntax_Print.term_to_string t  in
         let uu____14597 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____14595 uu____14597
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____14606 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____14606
        then
          let uu____14611 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____14611
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____14620 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____14620
         then
           let uu____14625 = FStar_Syntax_Print.term_to_string t  in
           let uu____14627 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____14625 uu____14627
         else ());
        (let univs2 = check_universe_generalization univnames1 gen1 t0  in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
         let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1  in
         (univs2, ts))))
  
let (gen :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_name
          Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____14711 =
          let uu____14713 =
            FStar_Util.for_all
              (fun uu____14727  ->
                 match uu____14727 with
                 | (uu____14737,uu____14738,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____14713  in
        if uu____14711
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____14790 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____14790
              then
                let uu____14793 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14793
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____14800 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____14800
               then
                 let uu____14803 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14803
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____14821 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____14821 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____14855 =
             match uu____14855 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____14892 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____14892
                   then
                     let uu____14897 =
                       let uu____14899 =
                         let uu____14903 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____14903
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____14899
                         (FStar_String.concat ", ")
                        in
                     let uu____14951 =
                       let uu____14953 =
                         let uu____14957 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____14957
                           (FStar_List.map
                              (fun u  ->
                                 let uu____14970 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____14972 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____14970
                                   uu____14972))
                          in
                       FStar_All.pipe_right uu____14953
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____14897
                       uu____14951
                   else ());
                  (let univs2 =
                     let uu____14986 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____14998 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____14998) univs1
                       uu____14986
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____15005 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____15005
                    then
                      let uu____15010 =
                        let uu____15012 =
                          let uu____15016 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____15016
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____15012
                          (FStar_String.concat ", ")
                         in
                      let uu____15064 =
                        let uu____15066 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____15080 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____15082 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____15080
                                    uu____15082))
                           in
                        FStar_All.pipe_right uu____15066
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____15010 uu____15064
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____15103 =
             let uu____15120 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____15120  in
           match uu____15103 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____15210 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____15210
                 then ()
                 else
                   (let uu____15215 = lec_hd  in
                    match uu____15215 with
                    | (lb1,uu____15223,uu____15224) ->
                        let uu____15225 = lec2  in
                        (match uu____15225 with
                         | (lb2,uu____15233,uu____15234) ->
                             let msg =
                               let uu____15237 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15239 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____15237 uu____15239
                                in
                             let uu____15242 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____15242))
                  in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun u  ->
                           FStar_All.pipe_right u21
                             (FStar_Util.for_some
                                (fun u'  ->
                                   FStar_Syntax_Unionfind.equiv
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                     u'.FStar_Syntax_Syntax.ctx_uvar_head))))
                    in
                 let uu____15310 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____15310
                 then ()
                 else
                   (let uu____15315 = lec_hd  in
                    match uu____15315 with
                    | (lb1,uu____15323,uu____15324) ->
                        let uu____15325 = lec2  in
                        (match uu____15325 with
                         | (lb2,uu____15333,uu____15334) ->
                             let msg =
                               let uu____15337 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15339 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15337 uu____15339
                                in
                             let uu____15342 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____15342))
                  in
               let lecs1 =
                 let uu____15353 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____15406 = univs_and_uvars_of_lec this_lec  in
                        match uu____15406 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____15353 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____15511 = lec_hd  in
                   match uu____15511 with
                   | (lbname,e,c) ->
                       let uu____15521 =
                         let uu____15527 =
                           let uu____15529 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____15531 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____15533 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____15529 uu____15531 uu____15533
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____15527)
                          in
                       let uu____15537 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____15521 uu____15537
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____15556 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____15556 with
                         | FStar_Pervasives_Native.Some uu____15565 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____15573 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____15577 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____15577 with
                              | (bs,kres) ->
                                  ((let uu____15597 =
                                      let uu____15598 =
                                        let uu____15601 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____15601
                                         in
                                      uu____15598.FStar_Syntax_Syntax.n  in
                                    match uu____15597 with
                                    | FStar_Syntax_Syntax.Tm_type uu____15602
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____15606 =
                                          let uu____15608 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____15608  in
                                        if uu____15606
                                        then fail1 kres
                                        else ()
                                    | uu____15613 -> fail1 kres);
                                   (let a =
                                      let uu____15615 =
                                        let uu____15618 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _15621  ->
                                             FStar_Pervasives_Native.Some
                                               _15621) uu____15618
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____15615
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15629 ->
                                          let uu____15630 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____15630
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_tot
                                                  kres))
                                       in
                                    FStar_Syntax_Util.set_uvar
                                      u.FStar_Syntax_Syntax.ctx_uvar_head t;
                                    (a,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag)))))))
                  in
               let gen_univs1 = gen_univs env univs1  in
               let gen_tvars = gen_types uvs  in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____15733  ->
                         match uu____15733 with
                         | (lbname,e,c) ->
                             let uu____15779 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____15840 ->
                                   let uu____15853 = (e, c)  in
                                   (match uu____15853 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Env.Beta;
                                            FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                                            FStar_TypeChecker_Env.CompressUvars;
                                            FStar_TypeChecker_Env.NoFullNorm;
                                            FStar_TypeChecker_Env.Exclude
                                              FStar_TypeChecker_Env.Zeta] env
                                            c
                                           in
                                        let e1 =
                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                            env e
                                           in
                                        let e2 =
                                          if is_rec
                                          then
                                            let tvar_args =
                                              FStar_List.map
                                                (fun uu____15893  ->
                                                   match uu____15893 with
                                                   | (x,uu____15899) ->
                                                       let uu____15900 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____15900)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____15918 =
                                                let uu____15920 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____15920
                                                 in
                                              if uu____15918
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  FStar_Pervasives_Native.None
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm  in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1  in
                                        let t =
                                          let uu____15929 =
                                            let uu____15930 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____15930.FStar_Syntax_Syntax.n
                                             in
                                          match uu____15929 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____15955 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____15955 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____15966 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____15970 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____15970, gen_tvars))
                                in
                             (match uu____15779 with
                              | (e1,c1,gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs))))
                  in
               FStar_Pervasives_Native.Some ecs)
  
let (generalize' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____16117 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____16117
         then
           let uu____16120 =
             let uu____16122 =
               FStar_List.map
                 (fun uu____16137  ->
                    match uu____16137 with
                    | (lb,uu____16146,uu____16147) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____16122 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____16120
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____16173  ->
                match uu____16173 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____16202 = gen env is_rec lecs  in
           match uu____16202 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16301  ->
                       match uu____16301 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____16363 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____16363
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____16411  ->
                           match uu____16411 with
                           | (l,us,e,c,gvs) ->
                               let uu____16445 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____16447 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____16449 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____16451 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16453 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____16445 uu____16447 uu____16449
                                 uu____16451 uu____16453))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____16498  ->
                match uu____16498 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____16542 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____16542, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (generalize :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____16597 =
          let uu____16601 =
            let uu____16603 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____16603  in
          FStar_Pervasives_Native.Some uu____16601  in
        FStar_Profiling.profile
          (fun uu____16620  -> generalize' env is_rec lecs) uu____16597
          "FStar.TypeChecker.Util.generalize"
  
let (check_has_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t2  ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check1 env2 t1 t21 =
            if env2.FStar_TypeChecker_Env.use_eq_strict
            then
              let uu____16677 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____16677 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____16683 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____16683
                    (fun _16686  -> FStar_Pervasives_Native.Some _16686)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____16695 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____16695 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____16701 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun _16704  -> FStar_Pervasives_Native.Some _16704)
                       uu____16701)
             in
          let uu____16705 = maybe_coerce_lc env1 e lc t2  in
          match uu____16705 with
          | (e1,lc1,g_c) ->
              let uu____16721 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____16721 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16730 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____16736 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____16730 uu____16736
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16745 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16745
                     then
                       let uu____16750 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16750
                     else ());
                    (let uu____16756 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____16756))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____16784 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____16784
         then
           let uu____16787 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16787
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____16801 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____16801 with
         | (c,g_c) ->
             let uu____16813 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____16813
             then
               let uu____16821 =
                 let uu____16823 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____16823  in
               (uu____16821, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____16831 =
                    let uu____16832 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____16832
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____16831
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____16833 = check_trivial_precondition env c1  in
                match uu____16833 with
                | (ct,vc,g_pre) ->
                    ((let uu____16849 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____16849
                      then
                        let uu____16854 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16854
                      else ());
                     (let uu____16859 =
                        let uu____16861 =
                          let uu____16862 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16862  in
                        discharge uu____16861  in
                      let uu____16863 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____16859, uu____16863)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_16897 =
        match uu___8_16897 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____16907)::[] -> f fst1
        | uu____16932 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____16944 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____16944
          (fun _16945  -> FStar_TypeChecker_Common.NonTrivial _16945)
         in
      let op_or_e e =
        let uu____16956 =
          let uu____16957 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____16957  in
        FStar_All.pipe_right uu____16956
          (fun _16960  -> FStar_TypeChecker_Common.NonTrivial _16960)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _16967  -> FStar_TypeChecker_Common.NonTrivial _16967)
         in
      let op_or_t t =
        let uu____16978 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____16978
          (fun _16981  -> FStar_TypeChecker_Common.NonTrivial _16981)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _16988  -> FStar_TypeChecker_Common.NonTrivial _16988)
         in
      let short_op_ite uu___9_16994 =
        match uu___9_16994 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____17004)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____17031)::[] ->
            let uu____17072 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____17072
              (fun _17073  -> FStar_TypeChecker_Common.NonTrivial _17073)
        | uu____17074 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____17086 =
          let uu____17094 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____17094)  in
        let uu____17102 =
          let uu____17112 =
            let uu____17120 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____17120)  in
          let uu____17128 =
            let uu____17138 =
              let uu____17146 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____17146)  in
            let uu____17154 =
              let uu____17164 =
                let uu____17172 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____17172)  in
              let uu____17180 =
                let uu____17190 =
                  let uu____17198 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____17198)  in
                [uu____17190; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____17164 :: uu____17180  in
            uu____17138 :: uu____17154  in
          uu____17112 :: uu____17128  in
        uu____17086 :: uu____17102  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____17260 =
            FStar_Util.find_map table
              (fun uu____17275  ->
                 match uu____17275 with
                 | (x,mk1) ->
                     let uu____17292 = FStar_Ident.lid_equals x lid  in
                     if uu____17292
                     then
                       let uu____17297 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____17297
                     else FStar_Pervasives_Native.None)
             in
          (match uu____17260 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17301 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____17309 =
      let uu____17310 = FStar_Syntax_Util.un_uinst l  in
      uu____17310.FStar_Syntax_Syntax.n  in
    match uu____17309 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17315 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____17351)::uu____17352 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____17371 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____17380,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____17381))::uu____17382 -> bs
      | uu____17400 ->
          let uu____17401 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____17401 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____17405 =
                 let uu____17406 = FStar_Syntax_Subst.compress t  in
                 uu____17406.FStar_Syntax_Syntax.n  in
               (match uu____17405 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____17410) ->
                    let uu____17431 =
                      FStar_Util.prefix_until
                        (fun uu___10_17471  ->
                           match uu___10_17471 with
                           | (uu____17479,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____17480)) ->
                               false
                           | uu____17485 -> true) bs'
                       in
                    (match uu____17431 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____17521,uu____17522) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____17594,uu____17595) ->
                         let uu____17668 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17688  ->
                                   match uu____17688 with
                                   | (x,uu____17697) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____17668
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17746  ->
                                     match uu____17746 with
                                     | (x,i) ->
                                         let uu____17765 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____17765, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17776 -> bs))
  
let (maybe_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c1  ->
        fun c2  ->
          fun t  ->
            let m1 = FStar_TypeChecker_Env.norm_eff_name env c1  in
            let m2 = FStar_TypeChecker_Env.norm_eff_name env c2  in
            let uu____17805 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____17805
            then e
            else
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (maybe_monadic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun t  ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c  in
          let uu____17836 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____17836
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (d : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "\027[01;36m%s\027[00m\n" s 
let (mk_toplevel_definition :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____17879 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____17879
         then
           ((let uu____17884 = FStar_Ident.text_of_lid lident  in
             d uu____17884);
            (let uu____17886 = FStar_Ident.text_of_lid lident  in
             let uu____17888 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____17886 uu____17888))
         else ());
        (let fv =
           let uu____17894 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____17894
             FStar_Pervasives_Native.None
            in
         let lbname = FStar_Util.Inr fv  in
         let lb =
           (false,
             [FStar_Syntax_Util.mk_letbinding lbname []
                FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def
                [] FStar_Range.dummyRange])
            in
         let sig_ctx =
           FStar_Syntax_Syntax.mk_sigelt
             (FStar_Syntax_Syntax.Sig_let (lb, [lident]))
            in
         let uu____17906 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2110_17908 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2110_17908.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2110_17908.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2110_17908.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2110_17908.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2110_17908.FStar_Syntax_Syntax.sigopts)
           }), uu____17906))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_17926 =
        match uu___11_17926 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17929 -> false  in
      let reducibility uu___12_17937 =
        match uu___12_17937 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____17944 -> false  in
      let assumption uu___13_17952 =
        match uu___13_17952 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____17956 -> false  in
      let reification uu___14_17964 =
        match uu___14_17964 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____17967 -> true
        | uu____17969 -> false  in
      let inferred uu___15_17977 =
        match uu___15_17977 with
        | FStar_Syntax_Syntax.Discriminator uu____17979 -> true
        | FStar_Syntax_Syntax.Projector uu____17981 -> true
        | FStar_Syntax_Syntax.RecordType uu____17987 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____17997 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____18010 -> false  in
      let has_eq uu___16_18018 =
        match uu___16_18018 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____18022 -> false  in
      let quals_combo_ok quals q =
        match q with
        | FStar_Syntax_Syntax.Assumption  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (inferred x))
                         || (visibility x))
                        || (assumption x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Inline_for_extraction)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.New  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (assumption x)))
        | FStar_Syntax_Syntax.Inline_for_extraction  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (visibility x))
                           || (reducibility x))
                          || (reification x))
                         || (inferred x))
                        || (has_eq x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Assumption)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Visible_default  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Irreducible  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Abstract  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Noeq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Unopteq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.TotalEffect  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (reification x)))
        | FStar_Syntax_Syntax.Logic  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((x = q) || (x = FStar_Syntax_Syntax.Assumption)) ||
                        (inferred x))
                       || (visibility x))
                      || (reducibility x)))
        | FStar_Syntax_Syntax.Reifiable  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Reflectable uu____18101 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18108 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____18141 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____18141))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____18172 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____18172
                       FStar_Parser_Const.erasable_attr)))
           in
        let se_has_erasable_attr =
          FStar_Syntax_Util.has_attribute se1.FStar_Syntax_Syntax.sigattrs
            FStar_Parser_Const.erasable_attr
           in
        if
          (val_exists && val_has_erasable_attr) &&
            (Prims.op_Negation se_has_erasable_attr)
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_QulifierListNotPermitted,
              "Mismatch of attributes between declaration and definition: Declaration is marked `erasable` but the definition is not")
            r
        else ();
        if
          (val_exists && (Prims.op_Negation val_has_erasable_attr)) &&
            se_has_erasable_attr
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_QulifierListNotPermitted,
              "Mismatch of attributed between declaration and definition: Definition is marked `erasable` but the declaration is not")
            r
        else ();
        if se_has_erasable_attr
        then
          (match se1.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_bundle uu____18192 ->
               let uu____18201 =
                 let uu____18203 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_18209  ->
                           match uu___17_18209 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____18212 -> false))
                    in
                 Prims.op_Negation uu____18203  in
               if uu____18201
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____18219 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____18226 -> ()
           | uu____18239 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_QulifierListNotPermitted,
                   "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions")
                 r)
        else ()  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____18253 =
        let uu____18255 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18261  ->
                  match uu___18_18261 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____18264 -> false))
           in
        FStar_All.pipe_right uu____18255 Prims.op_Negation  in
      if uu____18253
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____18285 =
            let uu____18291 =
              let uu____18293 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18293 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18291)  in
          FStar_Errors.raise_error uu____18285 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____18311 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18319 =
            let uu____18321 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____18321  in
          if uu____18319 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____18332),uu____18333) ->
              ((let uu____18345 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____18345
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____18354 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____18354
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____18365 ->
              ((let uu____18375 =
                  let uu____18377 =
                    FStar_All.pipe_right quals
                      (FStar_Util.for_all
                         (fun x  ->
                            (((((x = FStar_Syntax_Syntax.Abstract) ||
                                  (x =
                                     FStar_Syntax_Syntax.Inline_for_extraction))
                                 || (x = FStar_Syntax_Syntax.NoExtract))
                                || (inferred x))
                               || (visibility x))
                              || (has_eq x)))
                     in
                  Prims.op_Negation uu____18377  in
                if uu____18375 then err'1 () else ());
               (let uu____18387 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_18393  ->
                           match uu___19_18393 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____18396 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____18387
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____18402 ->
              let uu____18409 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____18409 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____18417 ->
              let uu____18424 =
                let uu____18426 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____18426  in
              if uu____18424 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____18436 ->
              let uu____18437 =
                let uu____18439 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____18439  in
              if uu____18437 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18449 ->
              let uu____18462 =
                let uu____18464 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____18464  in
              if uu____18462 then err'1 () else ()
          | uu____18474 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____18513 =
          let uu____18514 = FStar_Syntax_Subst.compress t1  in
          uu____18514.FStar_Syntax_Syntax.n  in
        match uu____18513 with
        | FStar_Syntax_Syntax.Tm_arrow uu____18518 ->
            let uu____18533 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____18533 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____18542;
               FStar_Syntax_Syntax.index = uu____18543;
               FStar_Syntax_Syntax.sort = t2;_},uu____18545)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____18554) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____18580) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____18586 -> false
      
      and aux env t1 =
        let t2 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Primops;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF;
            FStar_TypeChecker_Env.UnfoldUntil
              FStar_Syntax_Syntax.delta_constant;
            FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.AllowUnboundUniverses;
            FStar_TypeChecker_Env.Zeta;
            FStar_TypeChecker_Env.Iota;
            FStar_TypeChecker_Env.Unascribe] env t1
           in
        let res =
          (FStar_TypeChecker_Env.non_informative env t2) || (descend env t2)
           in
        (let uu____18596 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____18596
         then
           let uu____18601 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____18601
         else ());
        res
       in aux g t
  
let (fresh_effect_repr :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme ->
          FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ->
            FStar_Syntax_Syntax.universe ->
              FStar_Syntax_Syntax.term ->
                (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun r  ->
      fun eff_name  ->
        fun signature_ts  ->
          fun repr_ts_opt  ->
            fun u  ->
              fun a_tm  ->
                let fail1 t =
                  let uu____18666 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____18666 r  in
                let uu____18676 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____18676 with
                | (uu____18685,signature) ->
                    let uu____18687 =
                      let uu____18688 = FStar_Syntax_Subst.compress signature
                         in
                      uu____18688.FStar_Syntax_Syntax.n  in
                    (match uu____18687 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18696) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18744 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____18759 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____18761 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18759 eff_name.FStar_Ident.str
                                       uu____18761) r
                                 in
                              (match uu____18744 with
                               | (is,g) ->
                                   let uu____18774 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____18776 =
                                             let uu____18777 =
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 is
                                                in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = [u];
                                               FStar_Syntax_Syntax.effect_name
                                                 = eff_name;
                                               FStar_Syntax_Syntax.result_typ
                                                 = a_tm;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____18777;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18776
                                            in
                                         let uu____18796 =
                                           let uu____18803 =
                                             let uu____18804 =
                                               let uu____18819 =
                                                 let uu____18828 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____18828]  in
                                               (uu____18819, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____18804
                                              in
                                           FStar_Syntax_Syntax.mk uu____18803
                                            in
                                         uu____18796
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18859 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____18859
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____18868 =
                                           let uu____18873 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____18873
                                            in
                                         uu____18868
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____18774, g))
                          | uu____18882 -> fail1 signature)
                     | uu____18883 -> fail1 signature)
  
let (fresh_effect_repr_en :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun r  ->
      fun eff_name  ->
        fun u  ->
          fun a_tm  ->
            let uu____18914 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____18914
              (fun ed  ->
                 let uu____18922 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____18922 u a_tm)
  
let (layered_effect_indices_as_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun r  ->
      fun eff_name  ->
        fun sig_ts  ->
          fun u  ->
            fun a_tm  ->
              let uu____18958 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____18958 with
              | (uu____18963,sig_tm) ->
                  let fail1 t =
                    let uu____18971 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____18971 r  in
                  let uu____18977 =
                    let uu____18978 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____18978.FStar_Syntax_Syntax.n  in
                  (match uu____18977 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18982) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____19005)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____19027 -> fail1 sig_tm)
                   | uu____19028 -> fail1 sig_tm)
  
let (lift_tf_layered_effect :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun tgt  ->
    fun lift_ts  ->
      fun env  ->
        fun c  ->
          (let uu____19059 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____19059
           then
             let uu____19064 = FStar_Syntax_Print.comp_to_string c  in
             let uu____19066 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____19064 uu____19066
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____19073 =
             let uu____19084 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____19085 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____19084, (ct.FStar_Syntax_Syntax.result_typ), uu____19085)
              in
           match uu____19073 with
           | (u,a,c_is) ->
               let uu____19133 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____19133 with
                | (uu____19142,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____19153 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____19155 = FStar_Ident.string_of_lid tgt  in
                      let uu____19157 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____19153 uu____19155 s uu____19157
                       in
                    let uu____19160 =
                      let uu____19193 =
                        let uu____19194 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____19194.FStar_Syntax_Syntax.n  in
                      match uu____19193 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19258 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____19258 with
                           | (a_b::bs1,c2) ->
                               let uu____19318 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____19318, c2))
                      | uu____19406 ->
                          let uu____19407 =
                            let uu____19413 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____19413)
                             in
                          FStar_Errors.raise_error uu____19407 r
                       in
                    (match uu____19160 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____19531 =
                           let uu____19538 =
                             let uu____19539 =
                               let uu____19540 =
                                 let uu____19547 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____19547, a)  in
                               FStar_Syntax_Syntax.NT uu____19540  in
                             [uu____19539]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____19538
                             (fun b  ->
                                let uu____19564 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____19566 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____19568 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____19570 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____19564 uu____19566 uu____19568
                                  uu____19570) r
                            in
                         (match uu____19531 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____19584 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____19584
                                then
                                  let uu____19589 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____19598 =
                                             let uu____19600 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____19600
                                              in
                                           Prims.op_Hat s uu____19598) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____19589
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____19631 =
                                           let uu____19638 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____19638, t)  in
                                         FStar_Syntax_Syntax.NT uu____19631)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____19657 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____19657
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____19663 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____19663
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____19672 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____19672)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____19674 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____19674
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____19678 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____19678 r
                                   in
                                let fml =
                                  let uu____19683 =
                                    let uu____19688 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____19689 =
                                      let uu____19690 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____19690
                                       in
                                    (uu____19688, uu____19689)  in
                                  match uu____19683 with
                                  | (u1,wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange
                                   in
                                (let uu____19716 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____19716
                                 then
                                   let uu____19722 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____19722
                                 else ());
                                (let c1 =
                                   let uu____19728 =
                                     let uu____19729 =
                                       FStar_All.pipe_right is
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.as_arg)
                                        in
                                     {
                                       FStar_Syntax_Syntax.comp_univs =
                                         (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                       FStar_Syntax_Syntax.effect_name = tgt;
                                       FStar_Syntax_Syntax.result_typ = a;
                                       FStar_Syntax_Syntax.effect_args =
                                         uu____19729;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____19728
                                    in
                                 (let uu____19753 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____19753
                                  then
                                    let uu____19758 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____19758
                                  else ());
                                 (let uu____19763 =
                                    let uu____19764 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____19765 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____19764 uu____19765
                                     in
                                  (c1, uu____19763)))))))))
  
let lift_tf_layered_effect_term :
  'Auu____19779 .
    'Auu____19779 ->
      FStar_Syntax_Syntax.sub_eff ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun sub1  ->
      fun u  ->
        fun a  ->
          fun e  ->
            let lift =
              let uu____19808 =
                let uu____19813 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____19813
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____19808 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____19856 =
                let uu____19857 =
                  let uu____19860 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____19860
                    FStar_Syntax_Subst.compress
                   in
                uu____19857.FStar_Syntax_Syntax.n  in
              match uu____19856 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____19883::bs,uu____19885)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____19925 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____19925
                    FStar_Pervasives_Native.fst
              | uu____20031 ->
                  let uu____20032 =
                    let uu____20038 =
                      let uu____20040 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____20040
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____20038)  in
                  FStar_Errors.raise_error uu____20032
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____20067 = FStar_Syntax_Syntax.as_arg a  in
              let uu____20076 =
                let uu____20087 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____20123  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____20130 =
                  let uu____20141 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____20141]  in
                FStar_List.append uu____20087 uu____20130  in
              uu____20067 :: uu____20076  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
        let uu____20212 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____20212 with
        | (uu____20217,t) ->
            let err n1 =
              let uu____20227 =
                let uu____20233 =
                  let uu____20235 = FStar_Ident.string_of_lid datacon  in
                  let uu____20237 = FStar_Util.string_of_int n1  in
                  let uu____20239 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____20235 uu____20237 uu____20239
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____20233)
                 in
              let uu____20243 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____20227 uu____20243  in
            let uu____20244 =
              let uu____20245 = FStar_Syntax_Subst.compress t  in
              uu____20245.FStar_Syntax_Syntax.n  in
            (match uu____20244 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____20249) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20304  ->
                           match uu____20304 with
                           | (uu____20312,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____20321 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index1)
             | uu____20355 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____20368 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____20368
      then
        let uu____20371 =
          let uu____20384 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____20384
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____20371;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____20419 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____20419 with
           | (uu____20428,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____20447 =
                 let uu____20448 =
                   let uu___2486_20449 = ct  in
                   let uu____20450 =
                     let uu____20461 =
                       let uu____20470 =
                         let uu____20471 =
                           let uu____20478 =
                             let uu____20479 =
                               let uu____20496 =
                                 let uu____20507 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____20507; wp]  in
                               (lift_t, uu____20496)  in
                             FStar_Syntax_Syntax.Tm_app uu____20479  in
                           FStar_Syntax_Syntax.mk uu____20478  in
                         uu____20471 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____20470
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____20461]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2486_20449.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2486_20449.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____20450;
                     FStar_Syntax_Syntax.flags =
                       (uu___2486_20449.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____20448  in
               (uu____20447, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____20607 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____20607 with
           | (uu____20614,lift_t) ->
               let uu____20616 =
                 let uu____20623 =
                   let uu____20624 =
                     let uu____20641 =
                       let uu____20652 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____20661 =
                         let uu____20672 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____20681 =
                           let uu____20692 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____20692]  in
                         uu____20672 :: uu____20681  in
                       uu____20652 :: uu____20661  in
                     (lift_t, uu____20641)  in
                   FStar_Syntax_Syntax.Tm_app uu____20624  in
                 FStar_Syntax_Syntax.mk uu____20623  in
               uu____20616 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____20745 =
           let uu____20758 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____20758 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____20745;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____20794  ->
                        fun uu____20795  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub1  ->
      let uu____20818 = get_mlift_for_subeff env sub1  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub1.FStar_Syntax_Syntax.source sub1.FStar_Syntax_Syntax.target
        uu____20818
  
let (update_env_polymonadic_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun ty  ->
            FStar_TypeChecker_Env.add_polymonadic_bind env m n1 p
              (fun env1  ->
                 fun c1  ->
                   fun bv_opt  ->
                     fun c2  ->
                       fun flags  ->
                         fun r  ->
                           mk_indexed_bind env1 m n1 p ty c1 bv_opt c2 flags
                             r)
  