open Prims
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.unfold_whnf'
    [FStar_TypeChecker_Env.AllowUnboundUniverses]
  
let (tc_tycon :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_TypeChecker_Env.env_t * FStar_Syntax_Syntax.sigelt *
        FStar_Syntax_Syntax.universe * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ (tc,uvs,tps,k,mutuals,data) ->
          let env0 = env  in
          let uu____50 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____50 with
           | (usubst,uvs1) ->
               let uu____77 =
                 let uu____84 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                    in
                 let uu____85 = FStar_Syntax_Subst.subst_binders usubst tps
                    in
                 let uu____86 =
                   let uu____87 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____87 k  in
                 (uu____84, uu____85, uu____86)  in
               (match uu____77 with
                | (env1,tps1,k1) ->
                    let uu____107 = FStar_Syntax_Subst.open_term tps1 k1  in
                    (match uu____107 with
                     | (tps2,k2) ->
                         let uu____122 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____122 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____143 =
                                let uu____162 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2
                                   in
                                match uu____162 with
                                | (k3,uu____188,g) ->
                                    let k4 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Exclude
                                           FStar_TypeChecker_Env.Iota;
                                        FStar_TypeChecker_Env.Exclude
                                          FStar_TypeChecker_Env.Zeta;
                                        FStar_TypeChecker_Env.Eager_unfolding;
                                        FStar_TypeChecker_Env.NoFullNorm;
                                        FStar_TypeChecker_Env.Exclude
                                          FStar_TypeChecker_Env.Beta] env_tps
                                        k3
                                       in
                                    let uu____191 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____206 =
                                      let uu____207 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____207
                                       in
                                    (uu____191, uu____206)
                                 in
                              (match uu____143 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____270 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____270
                                      in
                                   let uu____273 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____273 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____291 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____291))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____298 =
                                              let uu____304 =
                                                let uu____306 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____308 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____306 uu____308
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____304)
                                               in
                                            FStar_Errors.raise_error
                                              uu____298
                                              s.FStar_Syntax_Syntax.sigrng)
                                         else ();
                                         (let usubst1 =
                                            FStar_Syntax_Subst.univ_var_closing
                                              uvs1
                                             in
                                          let guard1 =
                                            FStar_TypeChecker_Util.close_guard_implicits
                                              env1 false tps3 guard
                                             in
                                          let t_tc =
                                            let uu____322 =
                                              let uu____331 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____348 =
                                                let uu____357 =
                                                  let uu____370 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____370
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____357
                                                 in
                                              FStar_List.append uu____331
                                                uu____348
                                               in
                                            let uu____393 =
                                              let uu____396 =
                                                let uu____397 =
                                                  let uu____402 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____402
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____397
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____396
                                               in
                                            FStar_Syntax_Util.arrow uu____322
                                              uu____393
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____419 =
                                            let uu____424 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____425 =
                                              let uu____426 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____426 k4
                                               in
                                            (uu____424, uu____425)  in
                                          match uu____419 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____446 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____446,
                                                (let uu___61_452 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___61_452.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___61_452.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___61_452.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___61_452.FStar_Syntax_Syntax.sigattrs);
                                                   FStar_Syntax_Syntax.sigopts
                                                     =
                                                     (uu___61_452.FStar_Syntax_Syntax.sigopts)
                                                 }), u, guard1)))))))))
      | uu____457 -> failwith "impossible"
  
let (tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun tcs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon (c,_uvs,t,tc_lid,ntps,_mutual_tcs)
            ->
            let uu____521 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____521 with
             | (usubst,_uvs1) ->
                 let uu____544 =
                   let uu____549 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____550 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____549, uu____550)  in
                 (match uu____544 with
                  | (env1,t1) ->
                      let uu____557 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____596  ->
                               match uu____596 with
                               | (se1,u_tc) ->
                                   let uu____611 =
                                     let uu____613 =
                                       let uu____614 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____614  in
                                     FStar_Ident.lid_equals tc_lid uu____613
                                      in
                                   if uu____611
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____634,uu____635,tps,uu____637,uu____638,uu____639)
                                          ->
                                          let tps1 =
                                            let uu____649 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____649
                                              (FStar_List.map
                                                 (fun uu____689  ->
                                                    match uu____689 with
                                                    | (x,uu____703) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____711 =
                                            let uu____718 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____718, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____711
                                      | uu____725 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____768 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____768
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____557 with
                       | (env2,tps,u_tc) ->
                           let uu____800 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____808 =
                               let uu____809 = FStar_Syntax_Subst.compress t2
                                  in
                               uu____809.FStar_Syntax_Syntax.n  in
                             match uu____808 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____840 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____840 with
                                  | (uu____873,bs') ->
                                      let t3 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (bs', res))
                                          t2.FStar_Syntax_Syntax.pos
                                         in
                                      let subst1 =
                                        FStar_All.pipe_right tps
                                          (FStar_List.mapi
                                             (fun i  ->
                                                fun uu____944  ->
                                                  match uu____944 with
                                                  | (x,uu____953) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            (Prims.int_one +
                                                               i)), x)))
                                         in
                                      let uu____960 =
                                        let uu____965 =
                                          FStar_Syntax_Subst.subst subst1 t3
                                           in
                                        FStar_Syntax_Util.arrow_formals_comp
                                          uu____965
                                         in
                                      (match uu____960 with
                                       | (bs1,c1) ->
                                           let uu____974 =
                                             (FStar_Options.ml_ish ()) ||
                                               (FStar_Syntax_Util.is_total_comp
                                                  c1)
                                              in
                                           if uu____974
                                           then
                                             (bs1,
                                               (FStar_Syntax_Util.comp_result
                                                  c1))
                                           else
                                             (let uu____987 =
                                                FStar_Ident.range_of_lid
                                                  (FStar_Syntax_Util.comp_effect_name
                                                     c1)
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                  "Constructors cannot have effects")
                                                uu____987)))
                             | uu____996 -> ([], t2)  in
                           (match uu____800 with
                            | (arguments,result) ->
                                ((let uu____1016 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____1016
                                  then
                                    let uu____1019 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____1021 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____1024 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____1019 uu____1021 uu____1024
                                  else ());
                                 (let uu____1029 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____1029 with
                                  | (arguments1,env',us) ->
                                      let type_u_tc =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_type u_tc)
                                          result.FStar_Syntax_Syntax.pos
                                         in
                                      let env'1 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          env' type_u_tc
                                         in
                                      let uu____1047 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____1047 with
                                       | (result1,res_lcomp) ->
                                           let uu____1058 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____1058 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____1116 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____1116
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____1198  ->
                                                      fun uu____1199  ->
                                                        match (uu____1198,
                                                                uu____1199)
                                                        with
                                                        | ((bv,uu____1229),
                                                           (t2,uu____1231))
                                                            ->
                                                            let uu____1258 =
                                                              let uu____1259
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____1259.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____1258
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____1263 ->
                                                                 let uu____1264
                                                                   =
                                                                   let uu____1270
                                                                    =
                                                                    let uu____1272
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____1274
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____1272
                                                                    uu____1274
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____1270)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____1264
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____1279 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_TypeChecker_Common.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1279
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____1281 =
                                                     let uu____1282 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____1282.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____1281 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____1285 -> ()
                                                   | uu____1286 ->
                                                       let uu____1287 =
                                                         let uu____1293 =
                                                           let uu____1295 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____1297 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____1295
                                                             uu____1297
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____1293)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____1287
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____1302 =
                                                       let uu____1303 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____1303.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____1302 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____1307;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____1308;_},tuvs)
                                                         when
                                                         FStar_Syntax_Syntax.fv_eq_lid
                                                           fv tc_lid
                                                         ->
                                                         if
                                                           (FStar_List.length
                                                              _uvs1)
                                                             =
                                                             (FStar_List.length
                                                                tuvs)
                                                         then
                                                           FStar_List.fold_left2
                                                             (fun g  ->
                                                                fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____1322
                                                                    =
                                                                    let uu____1323
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____1324
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env'1
                                                                    uu____1323
                                                                    uu____1324
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1322)
                                                             FStar_TypeChecker_Env.trivial_guard
                                                             tuvs _uvs1
                                                         else
                                                           FStar_Errors.raise_error
                                                             (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                               "Length of annotated universes does not match inferred universes")
                                                             se.FStar_Syntax_Syntax.sigrng
                                                     | FStar_Syntax_Syntax.Tm_fvar
                                                         fv when
                                                         FStar_Syntax_Syntax.fv_eq_lid
                                                           fv tc_lid
                                                         ->
                                                         FStar_TypeChecker_Env.trivial_guard
                                                     | uu____1330 ->
                                                         let uu____1331 =
                                                           let uu____1337 =
                                                             let uu____1339 =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____1341 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____1339
                                                               uu____1341
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____1337)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____1331
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____1359  ->
                                                            fun u_x  ->
                                                              match uu____1359
                                                              with
                                                              | (x,uu____1368)
                                                                  ->
                                                                  let uu____1373
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1373)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____1377 =
                                                       let uu____1386 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun uu____1426
                                                                  ->
                                                                 match uu____1426
                                                                 with
                                                                 | (x,uu____1440)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____1386
                                                         arguments1
                                                        in
                                                     let uu____1454 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____1377 uu____1454
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___187_1459 = se
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.sigel
                                                         =
                                                         (FStar_Syntax_Syntax.Sig_datacon
                                                            (c, _uvs1, t3,
                                                              tc_lid, ntps,
                                                              []));
                                                       FStar_Syntax_Syntax.sigrng
                                                         =
                                                         (uu___187_1459.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___187_1459.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___187_1459.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___187_1459.FStar_Syntax_Syntax.sigattrs);
                                                       FStar_Syntax_Syntax.sigopts
                                                         =
                                                         (uu___187_1459.FStar_Syntax_Syntax.sigopts)
                                                     }), g))))))))))))
        | uu____1463 -> failwith "impossible"
  
let (generalize_and_inst_within :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
          Prims.list))
  =
  fun env  ->
    fun tcs  ->
      fun datas  ->
        let binders =
          FStar_All.pipe_right tcs
            (FStar_List.map
               (fun uu____1554  ->
                  match uu____1554 with
                  | (se,uu____1560) ->
                      (match se.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (uu____1561,uu____1562,tps,k,uu____1565,uu____1566)
                           ->
                           let uu____1575 =
                             let uu____1576 = FStar_Syntax_Syntax.mk_Total k
                                in
                             FStar_All.pipe_left
                               (FStar_Syntax_Util.arrow tps) uu____1576
                              in
                           FStar_Syntax_Syntax.null_binder uu____1575
                       | uu____1581 -> failwith "Impossible")))
           in
        let binders' =
          FStar_All.pipe_right datas
            (FStar_List.map
               (fun se  ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____1610,uu____1611,t,uu____1613,uu____1614,uu____1615)
                      -> FStar_Syntax_Syntax.null_binder t
                  | uu____1622 -> failwith "Impossible"))
           in
        let t =
          let uu____1627 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
          FStar_Syntax_Util.arrow (FStar_List.append binders binders')
            uu____1627
           in
        (let uu____1637 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "GenUniverses")
            in
         if uu____1637
         then
           let uu____1642 = FStar_TypeChecker_Normalize.term_to_string env t
              in
           FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n"
             uu____1642
         else ());
        (let uu____1647 = FStar_TypeChecker_Util.generalize_universes env t
            in
         match uu____1647 with
         | (uvs,t1) ->
             ((let uu____1667 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "GenUniverses")
                  in
               if uu____1667
               then
                 let uu____1672 =
                   let uu____1674 =
                     FStar_All.pipe_right uvs
                       (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                      in
                   FStar_All.pipe_right uu____1674 (FStar_String.concat ", ")
                    in
                 let uu____1691 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                   uu____1672 uu____1691
               else ());
              (let uu____1696 = FStar_Syntax_Subst.open_univ_vars uvs t1  in
               match uu____1696 with
               | (uvs1,t2) ->
                   let uu____1711 = FStar_Syntax_Util.arrow_formals t2  in
                   (match uu____1711 with
                    | (args,uu____1727) ->
                        let uu____1732 =
                          FStar_Util.first_N (FStar_List.length binders) args
                           in
                        (match uu____1732 with
                         | (tc_types,data_types) ->
                             let tcs1 =
                               FStar_List.map2
                                 (fun uu____1837  ->
                                    fun uu____1838  ->
                                      match (uu____1837, uu____1838) with
                                      | ((x,uu____1860),(se,uu____1862)) ->
                                          (match se.FStar_Syntax_Syntax.sigel
                                           with
                                           | FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc,uu____1878,tps,uu____1880,mutuals,datas1)
                                               ->
                                               let ty =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs1
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               let uu____1892 =
                                                 let uu____1897 =
                                                   let uu____1898 =
                                                     FStar_Syntax_Subst.compress
                                                       ty
                                                      in
                                                   uu____1898.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____1897 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (binders1,c) ->
                                                     let uu____1927 =
                                                       FStar_Util.first_N
                                                         (FStar_List.length
                                                            tps) binders1
                                                        in
                                                     (match uu____1927 with
                                                      | (tps1,rest) ->
                                                          let t3 =
                                                            match rest with
                                                            | [] ->
                                                                FStar_Syntax_Util.comp_result
                                                                  c
                                                            | uu____2005 ->
                                                                FStar_Syntax_Syntax.mk
                                                                  (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                  (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                             in
                                                          (tps1, t3))
                                                 | uu____2024 -> ([], ty)  in
                                               (match uu____1892 with
                                                | (tps1,t3) ->
                                                    let uu___264_2033 = se
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.sigel
                                                        =
                                                        (FStar_Syntax_Syntax.Sig_inductive_typ
                                                           (tc, uvs1, tps1,
                                                             t3, mutuals,
                                                             datas1));
                                                      FStar_Syntax_Syntax.sigrng
                                                        =
                                                        (uu___264_2033.FStar_Syntax_Syntax.sigrng);
                                                      FStar_Syntax_Syntax.sigquals
                                                        =
                                                        (uu___264_2033.FStar_Syntax_Syntax.sigquals);
                                                      FStar_Syntax_Syntax.sigmeta
                                                        =
                                                        (uu___264_2033.FStar_Syntax_Syntax.sigmeta);
                                                      FStar_Syntax_Syntax.sigattrs
                                                        =
                                                        (uu___264_2033.FStar_Syntax_Syntax.sigattrs);
                                                      FStar_Syntax_Syntax.sigopts
                                                        =
                                                        (uu___264_2033.FStar_Syntax_Syntax.sigopts)
                                                    })
                                           | uu____2038 ->
                                               failwith "Impossible"))
                                 tc_types tcs
                                in
                             let datas1 =
                               match uvs1 with
                               | [] -> datas
                               | uu____2045 ->
                                   let uvs_universes =
                                     FStar_All.pipe_right uvs1
                                       (FStar_List.map
                                          (fun _2049  ->
                                             FStar_Syntax_Syntax.U_name _2049))
                                      in
                                   let tc_insts =
                                     FStar_All.pipe_right tcs1
                                       (FStar_List.map
                                          (fun uu___0_2069  ->
                                             match uu___0_2069 with
                                             | {
                                                 FStar_Syntax_Syntax.sigel =
                                                   FStar_Syntax_Syntax.Sig_inductive_typ
                                                   (tc,uu____2075,uu____2076,uu____2077,uu____2078,uu____2079);
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____2080;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = uu____2081;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   = uu____2082;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = uu____2083;
                                                 FStar_Syntax_Syntax.sigopts
                                                   = uu____2084;_}
                                                 -> (tc, uvs_universes)
                                             | uu____2099 ->
                                                 failwith "Impossible"))
                                      in
                                   FStar_List.map2
                                     (fun uu____2123  ->
                                        fun d  ->
                                          match uu____2123 with
                                          | (t3,uu____2132) ->
                                              (match d.FStar_Syntax_Syntax.sigel
                                               with
                                               | FStar_Syntax_Syntax.Sig_datacon
                                                   (l,uu____2138,uu____2139,tc,ntps,mutuals)
                                                   ->
                                                   let ty =
                                                     let uu____2150 =
                                                       FStar_Syntax_InstFV.instantiate
                                                         tc_insts
                                                         t3.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____2150
                                                       (FStar_Syntax_Subst.close_univ_vars
                                                          uvs1)
                                                      in
                                                   let uu___301_2151 = d  in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (l, uvs1, ty, tc,
                                                            ntps, mutuals));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___301_2151.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___301_2151.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___301_2151.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___301_2151.FStar_Syntax_Syntax.sigattrs);
                                                     FStar_Syntax_Syntax.sigopts
                                                       =
                                                       (uu___301_2151.FStar_Syntax_Syntax.sigopts)
                                                   }
                                               | uu____2155 ->
                                                   failwith "Impossible"))
                                     data_types datas
                                in
                             (tcs1, datas1))))))
  
let (debug_log :
  FStar_TypeChecker_Env.env_t -> (unit -> Prims.string) -> unit) =
  fun env  ->
    fun msg  ->
      let uu____2179 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____2179
      then
        let uu____2184 =
          let uu____2186 =
            let uu____2188 = msg ()  in Prims.op_Hat uu____2188 "\n"  in
          Prims.op_Hat "Positivity::" uu____2186  in
        FStar_Util.print_string uu____2184
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____2207 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____2207
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____2224 =
      let uu____2225 = FStar_Syntax_Subst.compress t  in
      uu____2225.FStar_Syntax_Syntax.n  in
    match uu____2224 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____2244 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____2250 -> failwith "Node is not an fvar or a Tm_uinst"
  
type unfolded_memo_elt =
  (FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list
type unfolded_memo_t = unfolded_memo_elt FStar_ST.ref
let (already_unfolded :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ilid  ->
    fun arrghs  ->
      fun unfolded  ->
        fun env  ->
          let uu____2287 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____2336  ->
               match uu____2336 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2380 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____2380  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2287
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          debug_log env
            (fun uu____2587  ->
               let uu____2588 = FStar_Syntax_Print.term_to_string btype  in
               Prims.op_Hat "Checking strict positivity in type: " uu____2588);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.Eager_unfolding;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.Iota;
               FStar_TypeChecker_Env.Zeta;
               FStar_TypeChecker_Env.AllowUnboundUniverses] env btype
              in
           debug_log env
             (fun uu____2595  ->
                let uu____2596 = FStar_Syntax_Print.term_to_string btype1  in
                Prims.op_Hat
                  "Checking strict positivity in type, after normalization: "
                  uu____2596);
           (let uu____2601 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2601) ||
             ((debug_log env
                 (fun uu____2614  ->
                    "ty does occur in this type, pressing ahead");
               (let uu____2616 =
                  let uu____2617 = FStar_Syntax_Subst.compress btype1  in
                  uu____2617.FStar_Syntax_Syntax.n  in
                match uu____2616 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2647 = try_get_fv t  in
                    (match uu____2647 with
                     | (fv,us) ->
                         let uu____2655 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2655
                         then
                           (debug_log env
                              (fun uu____2661  ->
                                 "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
                            FStar_List.for_all
                              (fun uu____2673  ->
                                 match uu____2673 with
                                 | (t1,uu____2682) ->
                                     let uu____2687 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2687) args)
                         else
                           (debug_log env
                              (fun uu____2693  ->
                                 "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env
                       (fun uu____2719  ->
                          "Checking strict positivity in Tm_arrow");
                     (let check_comp1 =
                        let c1 =
                          let uu____2726 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____2726
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2730 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____2730
                             (FStar_List.existsb
                                (fun q  ->
                                   q = FStar_Syntax_Syntax.TotalEffect)))
                         in
                      if Prims.op_Negation check_comp1
                      then
                        (debug_log env
                           (fun uu____2742  ->
                              "Checking strict positivity , the arrow is impure, so return true");
                         true)
                      else
                        (debug_log env
                           (fun uu____2749  ->
                              "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
                         (FStar_List.for_all
                            (fun uu____2761  ->
                               match uu____2761 with
                               | (b,uu____2770) ->
                                   let uu____2775 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2775) sbs)
                           &&
                           ((let uu____2781 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2781 with
                             | (uu____2787,return_type) ->
                                 let uu____2789 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2789)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2790 ->
                    (debug_log env
                       (fun uu____2793  ->
                          "Checking strict positivity in an fvar, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2796 ->
                    (debug_log env
                       (fun uu____2799  ->
                          "Checking strict positivity in an Tm_type, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2803) ->
                    (debug_log env
                       (fun uu____2810  ->
                          "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2813) ->
                    (debug_log env
                       (fun uu____2820  ->
                          "Checking strict positivity in an Tm_refine, recur in the bv sort)");
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2822,branches) ->
                    (debug_log env
                       (fun uu____2862  ->
                          "Checking strict positivity in an Tm_match, recur in the branches)");
                     FStar_List.for_all
                       (fun uu____2883  ->
                          match uu____2883 with
                          | (p,uu____2896,t) ->
                              let bs =
                                let uu____2915 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2915
                                 in
                              let uu____2924 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2924 with
                               | (bs1,t1) ->
                                   let uu____2932 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2932)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2934,uu____2935)
                    ->
                    (debug_log env
                       (fun uu____2978  ->
                          "Checking strict positivity in an Tm_ascribed, recur)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2980 ->
                    (debug_log env
                       (fun uu____2984  ->
                          let uu____2985 =
                            let uu____2987 =
                              FStar_Syntax_Print.tag_of_term btype1  in
                            let uu____2989 =
                              let uu____2991 =
                                FStar_Syntax_Print.term_to_string btype1  in
                              Prims.op_Hat " and term: " uu____2991  in
                            Prims.op_Hat uu____2987 uu____2989  in
                          Prims.op_Hat
                            "Checking strict positivity, unexpected tag: "
                            uu____2985);
                     false)))))

and (ty_nested_positive_in_inductive :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universes ->
        FStar_Syntax_Syntax.args ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun ilid  ->
      fun us  ->
        fun args  ->
          fun unfolded  ->
            fun env  ->
              debug_log env
                (fun uu____3006  ->
                   let uu____3007 =
                     let uu____3009 =
                       let uu____3011 =
                         FStar_Syntax_Print.args_to_string args  in
                       Prims.op_Hat " applied to arguments: " uu____3011  in
                     Prims.op_Hat ilid.FStar_Ident.str uu____3009  in
                   Prims.op_Hat
                     "Checking nested positivity in the inductive "
                     uu____3007);
              (let uu____3015 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____3015 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____3034 =
                       let uu____3036 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____3036
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____3034
                      then
                        (debug_log env
                           (fun uu____3042  ->
                              let uu____3043 = FStar_Ident.string_of_lid ilid
                                 in
                              FStar_Util.format1
                                "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                                uu____3043);
                         true)
                      else
                        (debug_log env
                           (fun uu____3051  ->
                              "Checking nested positivity, not an inductive, return false");
                         false))
                   else
                     (let uu____3056 =
                        already_unfolded ilid args unfolded env  in
                      if uu____3056
                      then
                        (debug_log env
                           (fun uu____3062  ->
                              "Checking nested positivity, we have already unfolded this inductive with these args");
                         true)
                      else
                        (let num_ibs =
                           let uu____3069 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____3069  in
                         debug_log env
                           (fun uu____3077  ->
                              let uu____3078 =
                                let uu____3080 =
                                  FStar_Util.string_of_int num_ibs  in
                                Prims.op_Hat uu____3080
                                  ", also adding to the memo table"
                                 in
                              Prims.op_Hat
                                "Checking nested positivity, number of type parameters is "
                                uu____3078);
                         (let uu____3085 =
                            let uu____3086 = FStar_ST.op_Bang unfolded  in
                            let uu____3112 =
                              let uu____3119 =
                                let uu____3124 =
                                  let uu____3125 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____3125  in
                                (ilid, uu____3124)  in
                              [uu____3119]  in
                            FStar_List.append uu____3086 uu____3112  in
                          FStar_ST.op_Colon_Equals unfolded uu____3085);
                         FStar_List.for_all
                           (fun d  ->
                              ty_nested_positive_in_dlid ty_lid d ilid us
                                args num_ibs unfolded env) idatas)))

and (ty_nested_positive_in_dlid :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            Prims.int ->
              unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun dlid  ->
      fun ilid  ->
        fun us  ->
          fun args  ->
            fun num_ibs  ->
              fun unfolded  ->
                fun env  ->
                  debug_log env
                    (fun uu____3223  ->
                       Prims.op_Hat
                         "Checking nested positivity in data constructor "
                         (Prims.op_Hat dlid.FStar_Ident.str
                            (Prims.op_Hat " of the inductive "
                               ilid.FStar_Ident.str)));
                  (let uu____3226 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____3226 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3249 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us;
                        (let dt1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant;
                             FStar_TypeChecker_Env.Iota;
                             FStar_TypeChecker_Env.Zeta;
                             FStar_TypeChecker_Env.AllowUnboundUniverses] env
                             dt
                            in
                         debug_log env
                           (fun uu____3255  ->
                              let uu____3256 =
                                FStar_Syntax_Print.term_to_string dt1  in
                              Prims.op_Hat
                                "Checking nested positivity in the data constructor type: "
                                uu____3256);
                         (let uu____3259 =
                            let uu____3260 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____3260.FStar_Syntax_Syntax.n  in
                          match uu____3259 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 (fun uu____3288  ->
                                    "Checked nested positivity in Tm_arrow data constructor type");
                               (let uu____3290 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____3290 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____3354 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3354 dbs1
                                       in
                                    let c1 =
                                      let uu____3358 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3358 c
                                       in
                                    let uu____3361 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3361 with
                                     | (args1,uu____3396) ->
                                         let subst1 =
                                           FStar_List.fold_left2
                                             (fun subst1  ->
                                                fun ib  ->
                                                  fun arg  ->
                                                    FStar_List.append subst1
                                                      [FStar_Syntax_Syntax.NT
                                                         ((FStar_Pervasives_Native.fst
                                                             ib),
                                                           (FStar_Pervasives_Native.fst
                                                              arg))]) [] ibs1
                                             args1
                                            in
                                         let dbs3 =
                                           FStar_Syntax_Subst.subst_binders
                                             subst1 dbs2
                                            in
                                         let c2 =
                                           let uu____3488 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3488 c1
                                            in
                                         (debug_log env
                                            (fun uu____3500  ->
                                               let uu____3501 =
                                                 let uu____3503 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     "; " dbs3
                                                    in
                                                 let uu____3506 =
                                                   let uu____3508 =
                                                     FStar_Syntax_Print.comp_to_string
                                                       c2
                                                      in
                                                   Prims.op_Hat ", and c: "
                                                     uu____3508
                                                    in
                                                 Prims.op_Hat uu____3503
                                                   uu____3506
                                                  in
                                               Prims.op_Hat
                                                 "Checking nested positivity in the unfolded data constructor binders as: "
                                                 uu____3501);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3522 ->
                              (debug_log env
                                 (fun uu____3525  ->
                                    "Checking nested positivity in the data constructor type that is not an arrow");
                               (let uu____3527 =
                                  let uu____3528 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3528.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3527
                                  ilid num_ibs unfolded env))))))

and (ty_nested_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' ->
      FStar_Ident.lident ->
        Prims.int ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun t  ->
      fun ilid  ->
        fun num_ibs  ->
          fun unfolded  ->
            fun env  ->
              match t with
              | FStar_Syntax_Syntax.Tm_app (t1,args) ->
                  (debug_log env
                     (fun uu____3567  ->
                        "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself");
                   (let uu____3569 = try_get_fv t1  in
                    match uu____3569 with
                    | (fv,uu____3576) ->
                        let uu____3577 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3577
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  (debug_log env
                     (fun uu____3611  ->
                        let uu____3612 =
                          FStar_Syntax_Print.binders_to_string "; " sbs  in
                        Prims.op_Hat
                          "Checking nested positivity in an Tm_arrow node, with binders as: "
                          uu____3612);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3617 =
                      FStar_List.fold_left
                        (fun uu____3638  ->
                           fun b  ->
                             match uu____3638 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3669 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3673 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3669, uu____3673))) (true, env)
                        sbs1
                       in
                    match uu____3617 with | (b,uu____3691) -> b))
              | uu____3694 ->
                  failwith "Nested positive check, unhandled case"

let (ty_positive_in_datacon :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.universes ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env -> Prims.bool)
  =
  fun ty_lid  ->
    fun dlid  ->
      fun ty_bs  ->
        fun us  ->
          fun unfolded  ->
            fun env  ->
              let uu____3730 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3730 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3753 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   debug_log env
                     (fun uu____3758  ->
                        let uu____3759 = FStar_Syntax_Print.term_to_string dt
                           in
                        Prims.op_Hat "Checking data constructor type: "
                          uu____3759);
                   (let uu____3762 =
                      let uu____3763 = FStar_Syntax_Subst.compress dt  in
                      uu____3763.FStar_Syntax_Syntax.n  in
                    match uu____3762 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3767 ->
                        (debug_log env
                           (fun uu____3770  ->
                              "Data constructor type is simply an fvar, returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3774) ->
                        let dbs1 =
                          let uu____3804 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3804  in
                        let dbs2 =
                          let uu____3854 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3854 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        (debug_log env
                           (fun uu____3861  ->
                              let uu____3862 =
                                let uu____3864 =
                                  FStar_Util.string_of_int
                                    (FStar_List.length dbs3)
                                   in
                                Prims.op_Hat uu____3864 " binders"  in
                              Prims.op_Hat
                                "Data constructor type is an arrow type, so checking strict positivity in "
                                uu____3862);
                         (let uu____3874 =
                            FStar_List.fold_left
                              (fun uu____3895  ->
                                 fun b  ->
                                   match uu____3895 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3926 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3930 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3926, uu____3930)))
                              (true, env) dbs3
                             in
                          match uu____3874 with | (b,uu____3948) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3951,uu____3952) ->
                        (debug_log env
                           (fun uu____3979  ->
                              "Data constructor type is a Tm_app, so returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           (fun uu____3990  ->
                              "Data constructor type is a Tm_uinst, so recursing in the base type");
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3992 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____4015 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____4031,uu____4032,uu____4033) -> (lid, us, bs)
        | uu____4042 -> failwith "Impossible!"  in
      match uu____4015 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____4054 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____4054 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____4078 =
                 let uu____4081 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____4081  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____4095 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4095
                      unfolded_inductives env2) uu____4078)
  
let (check_exn_positivity :
  FStar_Ident.lid -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun data_ctor_lid  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      ty_positive_in_datacon FStar_Parser_Const.exn_lid data_ctor_lid [] []
        unfolded_inductives env
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4130,uu____4131,t,uu____4133,uu____4134,uu____4135) -> t
    | uu____4142 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____4159 =
         let uu____4161 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____4161 haseq_suffix  in
       uu____4159 = Prims.int_zero)
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____4171 =
      let uu____4174 =
        let uu____4177 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____4177]  in
      FStar_List.append lid.FStar_Ident.ns uu____4174  in
    FStar_Ident.lid_of_ids uu____4171
  
let (get_optimized_haseq_axiom :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_names ->
          (FStar_Ident.lident * FStar_Syntax_Syntax.term *
            FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders *
            FStar_Syntax_Syntax.term))
  =
  fun en  ->
    fun ty  ->
      fun usubst  ->
        fun us  ->
          let uu____4223 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____4237,bs,t,uu____4240,uu____4241) -> (lid, bs, t)
            | uu____4250 -> failwith "Impossible!"  in
          match uu____4223 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____4273 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____4273 t  in
              let uu____4282 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____4282 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____4300 =
                       let uu____4301 = FStar_Syntax_Subst.compress t2  in
                       uu____4301.FStar_Syntax_Syntax.n  in
                     match uu____4300 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4305) -> ibs
                     | uu____4326 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____4335 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____4336 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4335 uu____4336
                      in
                   let ind1 =
                     let uu____4340 =
                       FStar_List.map
                         (fun uu____4357  ->
                            match uu____4357 with
                            | (bv,aq) ->
                                let uu____4376 =
                                  FStar_Syntax_Syntax.bv_to_name bv  in
                                (uu____4376, aq)) bs2
                        in
                     FStar_Syntax_Syntax.mk_Tm_app ind uu____4340
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____4380 =
                       FStar_List.map
                         (fun uu____4397  ->
                            match uu____4397 with
                            | (bv,aq) ->
                                let uu____4416 =
                                  FStar_Syntax_Syntax.bv_to_name bv  in
                                (uu____4416, aq)) ibs1
                        in
                     FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4380
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____4420 =
                       let uu____4421 = FStar_Syntax_Syntax.as_arg ind2  in
                       [uu____4421]  in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                       uu____4420 FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4470 =
                            let uu____4471 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4471  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4470) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4484 =
                              let uu____4487 =
                                let uu____4488 =
                                  let uu____4497 =
                                    FStar_Syntax_Syntax.bv_to_name
                                      (FStar_Pervasives_Native.fst b)
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4497  in
                                [uu____4488]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.t_haseq uu____4487
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4484)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___667_4520 = fml  in
                     let uu____4521 =
                       let uu____4522 =
                         let uu____4529 =
                           let uu____4530 =
                             let uu____4551 =
                               FStar_Syntax_Syntax.binders_to_names ibs1  in
                             let uu____4556 =
                               let uu____4569 =
                                 let uu____4580 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind  in
                                 [uu____4580]  in
                               [uu____4569]  in
                             (uu____4551, uu____4556)  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4530  in
                         (fml, uu____4529)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4522  in
                     {
                       FStar_Syntax_Syntax.n = uu____4521;
                       FStar_Syntax_Syntax.pos =
                         (uu___667_4520.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___667_4520.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4649 =
                              let uu____4650 =
                                let uu____4659 =
                                  let uu____4660 =
                                    FStar_Syntax_Subst.close [b] t3  in
                                  FStar_Syntax_Util.abs
                                    [((FStar_Pervasives_Native.fst b),
                                       FStar_Pervasives_Native.None)]
                                    uu____4660 FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.as_arg uu____4659  in
                              [uu____4650]  in
                            FStar_Syntax_Syntax.mk_Tm_app
                              FStar_Syntax_Util.tforall uu____4649
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4713 =
                              let uu____4714 =
                                let uu____4723 =
                                  let uu____4724 =
                                    FStar_Syntax_Subst.close [b] t3  in
                                  FStar_Syntax_Util.abs
                                    [((FStar_Pervasives_Native.fst b),
                                       FStar_Pervasives_Native.None)]
                                    uu____4724 FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.as_arg uu____4723  in
                              [uu____4714]  in
                            FStar_Syntax_Syntax.mk_Tm_app
                              FStar_Syntax_Util.tforall uu____4713
                              FStar_Range.dummyRange) bs2 fml2
                      in
                   let axiom_lid = get_haseq_axiom_lid lid  in
                   (axiom_lid, fml3, bs2, ibs1, haseq_bs))
  
let (optimized_haseq_soundness_for_data :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term)
  =
  fun ty_lid  ->
    fun data  ->
      fun usubst  ->
        fun bs  ->
          let dt = datacon_typ data  in
          let dt1 = FStar_Syntax_Subst.subst usubst dt  in
          let uu____4799 =
            let uu____4800 = FStar_Syntax_Subst.compress dt1  in
            uu____4800.FStar_Syntax_Syntax.n  in
          match uu____4799 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4804) ->
              let dbs1 =
                let uu____4834 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4834  in
              let dbs2 =
                let uu____4884 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4884 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4897 =
                           let uu____4898 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           [uu____4898]  in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu____4897
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4929 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4929 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4937 =
                       let uu____4938 =
                         let uu____4947 =
                           let uu____4948 = FStar_Syntax_Subst.close [b] t
                              in
                           FStar_Syntax_Util.abs
                             [((FStar_Pervasives_Native.fst b),
                                FStar_Pervasives_Native.None)] uu____4948
                             FStar_Pervasives_Native.None
                            in
                         FStar_Syntax_Syntax.as_arg uu____4947  in
                       [uu____4938]  in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                       uu____4937 FStar_Range.dummyRange) dbs3 cond
          | uu____4995 -> FStar_Syntax_Util.t_true
  
let (optimized_haseq_ty :
  FStar_Syntax_Syntax.sigelts ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list *
          FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax) ->
          FStar_Syntax_Syntax.sigelt ->
            ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list *
              FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term'
              FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term'
              FStar_Syntax_Syntax.syntax))
  =
  fun all_datas_in_the_bundle  ->
    fun usubst  ->
      fun us  ->
        fun acc  ->
          fun ty  ->
            let lid =
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,uu____5086,uu____5087,uu____5088,uu____5089,uu____5090)
                  -> lid
              | uu____5099 -> failwith "Impossible!"  in
            let uu____5101 = acc  in
            match uu____5101 with
            | (uu____5138,en,uu____5140,uu____5141) ->
                let uu____5162 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____5162 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____5199 = acc  in
                     (match uu____5199 with
                      | (l_axioms,env,guard',cond') ->
                          let env1 =
                            FStar_TypeChecker_Env.push_binders env bs  in
                          let env2 =
                            FStar_TypeChecker_Env.push_binders env1 ibs  in
                          let t_datas =
                            FStar_List.filter
                              (fun s  ->
                                 match s.FStar_Syntax_Syntax.sigel with
                                 | FStar_Syntax_Syntax.Sig_datacon
                                     (uu____5274,uu____5275,uu____5276,t_lid,uu____5278,uu____5279)
                                     -> t_lid = lid
                                 | uu____5286 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____5301 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5301)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____5304 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____5307 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5304, uu____5307)))
  
let (optimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle  ->
    fun tcs  ->
      fun datas  ->
        fun env0  ->
          let uu____5365 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5375,us,uu____5377,t,uu____5379,uu____5380) -> 
                (us, t)
            | uu____5389 -> failwith "Impossible!"  in
          match uu____5365 with
          | (us,t) ->
              let uu____5399 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5399 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____5425 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____5425 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____5503 = FStar_Syntax_Util.arrow_formals t
                              in
                           match uu____5503 with
                           | (uu____5510,t1) ->
                               let uu____5516 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____5516
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____5521 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____5521 with
                          | (phi1,uu____5529) ->
                              ((let uu____5531 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____5531
                                then
                                  let uu____5534 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____5534
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____5552  ->
                                         match uu____5552 with
                                         | (lid,fml) ->
                                             let fml1 =
                                               FStar_Syntax_Subst.close_univ_vars
                                                 us1 fml
                                                in
                                             FStar_List.append l
                                               [{
                                                  FStar_Syntax_Syntax.sigel =
                                                    (FStar_Syntax_Syntax.Sig_assume
                                                       (lid, us1, fml1));
                                                  FStar_Syntax_Syntax.sigrng
                                                    = FStar_Range.dummyRange;
                                                  FStar_Syntax_Syntax.sigquals
                                                    = [];
                                                  FStar_Syntax_Syntax.sigmeta
                                                    =
                                                    FStar_Syntax_Syntax.default_sigmeta;
                                                  FStar_Syntax_Syntax.sigattrs
                                                    = [];
                                                  FStar_Syntax_Syntax.sigopts
                                                    =
                                                    FStar_Pervasives_Native.None
                                                }]) [] axioms
                                   in
                                (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                                  "haseq";
                                ses))))))
  
let (unoptimized_haseq_data :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lident Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun usubst  ->
    fun bs  ->
      fun haseq_ind  ->
        fun mutuals  ->
          fun acc  ->
            fun data  ->
              let rec is_mutual t =
                let uu____5624 =
                  let uu____5625 = FStar_Syntax_Subst.compress t  in
                  uu____5625.FStar_Syntax_Syntax.n  in
                match uu____5624 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5633) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5670 = is_mutual t'  in
                    if uu____5670
                    then true
                    else
                      (let uu____5677 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5677)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5697) -> is_mutual t'
                | uu____5702 -> false
              
              and exists_mutual uu___1_5704 =
                match uu___1_5704 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5725 =
                let uu____5726 = FStar_Syntax_Subst.compress dt1  in
                uu____5726.FStar_Syntax_Syntax.n  in
              match uu____5725 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5732) ->
                  let dbs1 =
                    let uu____5762 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5762  in
                  let dbs2 =
                    let uu____5812 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5812 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5830 =
                               let uu____5831 =
                                 FStar_Syntax_Syntax.as_arg
                                   (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                  in
                               [uu____5831]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.t_haseq uu____5830
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5861 = is_mutual sort  in
                             if uu____5861
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort  in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3
                     in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____5874 =
                             let uu____5875 =
                               let uu____5884 =
                                 let uu____5885 =
                                   FStar_Syntax_Subst.close [b] t  in
                                 FStar_Syntax_Util.abs
                                   [((FStar_Pervasives_Native.fst b),
                                      FStar_Pervasives_Native.None)]
                                   uu____5885 FStar_Pervasives_Native.None
                                  in
                               FStar_Syntax_Syntax.as_arg uu____5884  in
                             [uu____5875]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.tforall uu____5874
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5932 -> acc
  
let (unoptimized_haseq_ty :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Ident.lident Prims.list ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_name Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun all_datas_in_the_bundle  ->
    fun mutuals  ->
      fun usubst  ->
        fun us  ->
          fun acc  ->
            fun ty  ->
              let uu____5982 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____6004,bs,t,uu____6007,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____6019 -> failwith "Impossible!"  in
              match uu____5982 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____6043 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____6043 t  in
                  let uu____6052 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____6052 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____6062 =
                           let uu____6063 = FStar_Syntax_Subst.compress t2
                              in
                           uu____6063.FStar_Syntax_Syntax.n  in
                         match uu____6062 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____6067) ->
                             ibs
                         | uu____6088 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____6097 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____6098 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6097
                           uu____6098
                          in
                       let ind1 =
                         let uu____6102 =
                           FStar_List.map
                             (fun uu____6119  ->
                                match uu____6119 with
                                | (bv,aq) ->
                                    let uu____6138 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    (uu____6138, aq)) bs2
                            in
                         FStar_Syntax_Syntax.mk_Tm_app ind uu____6102
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____6142 =
                           FStar_List.map
                             (fun uu____6159  ->
                                match uu____6159 with
                                | (bv,aq) ->
                                    let uu____6178 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    (uu____6178, aq)) ibs1
                            in
                         FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6142
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____6182 =
                           let uu____6183 = FStar_Syntax_Syntax.as_arg ind2
                              in
                           [uu____6183]  in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu____6182
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6220,uu____6221,uu____6222,t_lid,uu____6224,uu____6225)
                                  -> t_lid = lid
                              | uu____6232 -> failwith "Impossible")
                           all_datas_in_the_bundle
                          in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas
                          in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind
                          in
                       let fml1 =
                         let uu___904_6244 = fml  in
                         let uu____6245 =
                           let uu____6246 =
                             let uu____6253 =
                               let uu____6254 =
                                 let uu____6275 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1
                                    in
                                 let uu____6280 =
                                   let uu____6293 =
                                     let uu____6304 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind
                                        in
                                     [uu____6304]  in
                                   [uu____6293]  in
                                 (uu____6275, uu____6280)  in
                               FStar_Syntax_Syntax.Meta_pattern uu____6254
                                in
                             (fml, uu____6253)  in
                           FStar_Syntax_Syntax.Tm_meta uu____6246  in
                         {
                           FStar_Syntax_Syntax.n = uu____6245;
                           FStar_Syntax_Syntax.pos =
                             (uu___904_6244.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___904_6244.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6373 =
                                  let uu____6374 =
                                    let uu____6383 =
                                      let uu____6384 =
                                        FStar_Syntax_Subst.close [b] t3  in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____6384
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____6383  in
                                  [uu____6374]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____6373
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6437 =
                                  let uu____6438 =
                                    let uu____6447 =
                                      let uu____6448 =
                                        FStar_Syntax_Subst.close [b] t3  in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____6448
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____6447  in
                                  [uu____6438]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____6437
                                  FStar_Range.dummyRange) bs2 fml2
                          in
                       FStar_Syntax_Util.mk_conj acc fml3)
  
let (unoptimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle  ->
    fun tcs  ->
      fun datas  ->
        fun env0  ->
          let mutuals =
            FStar_List.map
              (fun ty  ->
                 match ty.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____6540,uu____6541,uu____6542,uu____6543,uu____6544)
                     -> lid
                 | uu____6553 -> failwith "Impossible!") tcs
             in
          let uu____6555 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____6567,uu____6568,uu____6569,uu____6570) ->
                (lid, us)
            | uu____6579 -> failwith "Impossible!"  in
          match uu____6555 with
          | (lid,us) ->
              let uu____6589 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____6589 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____6616 =
                       let uu____6617 =
                         let uu____6624 = get_haseq_axiom_lid lid  in
                         (uu____6624, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____6617  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6616;
                       FStar_Syntax_Syntax.sigrng = FStar_Range.dummyRange;
                       FStar_Syntax_Syntax.sigquals = [];
                       FStar_Syntax_Syntax.sigmeta =
                         FStar_Syntax_Syntax.default_sigmeta;
                       FStar_Syntax_Syntax.sigattrs = [];
                       FStar_Syntax_Syntax.sigopts =
                         FStar_Pervasives_Native.None
                     }  in
                   [se])
  
let (check_inductive_well_typedness :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list
            * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let uu____6678 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___2_6704  ->
                    match uu___2_6704 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6706;
                        FStar_Syntax_Syntax.sigrng = uu____6707;
                        FStar_Syntax_Syntax.sigquals = uu____6708;
                        FStar_Syntax_Syntax.sigmeta = uu____6709;
                        FStar_Syntax_Syntax.sigattrs = uu____6710;
                        FStar_Syntax_Syntax.sigopts = uu____6711;_} -> true
                    | uu____6735 -> false))
             in
          match uu____6678 with
          | (tys,datas) ->
              ((let uu____6758 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3_6770  ->
                          match uu___3_6770 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6772;
                              FStar_Syntax_Syntax.sigrng = uu____6773;
                              FStar_Syntax_Syntax.sigquals = uu____6774;
                              FStar_Syntax_Syntax.sigmeta = uu____6775;
                              FStar_Syntax_Syntax.sigattrs = uu____6776;
                              FStar_Syntax_Syntax.sigopts = uu____6777;_} ->
                              false
                          | uu____6800 -> true))
                   in
                if uu____6758
                then
                  let uu____6803 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6803
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = Prims.int_zero
                  then []
                  else
                    (let uu____6818 =
                       let uu____6819 = FStar_List.hd tys  in
                       uu____6819.FStar_Syntax_Syntax.sigel  in
                     match uu____6818 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6822,uvs,uu____6824,uu____6825,uu____6826,uu____6827)
                         -> uvs
                     | uu____6836 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6841 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____6880  ->
                         match uu____6880 with
                         | (env1,all_tcs,g) ->
                             let uu____6920 = tc_tycon env1 tc  in
                             (match uu____6920 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u
                                     in
                                  ((let uu____6947 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low
                                       in
                                    if uu____6947
                                    then
                                      let uu____6950 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1
                                         in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____6950
                                    else ());
                                   (let uu____6955 =
                                      let uu____6956 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard g'
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____6956
                                       in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____6955))))) tys
                    (env, [], FStar_TypeChecker_Env.trivial_guard)
                   in
                match uu____6841 with
                | (env1,tcs,g) ->
                    let uu____7002 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____7024  ->
                             match uu____7024 with
                             | (datas1,g1) ->
                                 let uu____7043 =
                                   let uu____7048 = tc_data env1 tcs  in
                                   uu____7048 se  in
                                 (match uu____7043 with
                                  | (data,g') ->
                                      let uu____7065 =
                                        FStar_TypeChecker_Env.conj_guard g1
                                          g'
                                         in
                                      ((data :: datas1), uu____7065))) datas
                        ([], g)
                       in
                    (match uu____7002 with
                     | (datas1,g1) ->
                         let uu____7086 =
                           let tc_universe_vars =
                             FStar_List.map FStar_Pervasives_Native.snd tcs
                              in
                           let g2 =
                             let uu___1015_7103 = g1  in
                             {
                               FStar_TypeChecker_Common.guard_f =
                                 (uu___1015_7103.FStar_TypeChecker_Common.guard_f);
                               FStar_TypeChecker_Common.deferred =
                                 (uu___1015_7103.FStar_TypeChecker_Common.deferred);
                               FStar_TypeChecker_Common.univ_ineqs =
                                 (tc_universe_vars,
                                   (FStar_Pervasives_Native.snd
                                      g1.FStar_TypeChecker_Common.univ_ineqs));
                               FStar_TypeChecker_Common.implicits =
                                 (uu___1015_7103.FStar_TypeChecker_Common.implicits)
                             }  in
                           (let uu____7113 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "GenUniverses")
                               in
                            if uu____7113
                            then
                              let uu____7118 =
                                FStar_TypeChecker_Rel.guard_to_string env1 g2
                                 in
                              FStar_Util.print1
                                "@@@@@@Guard before (possible) generalization: %s\n"
                                uu____7118
                            else ());
                           FStar_TypeChecker_Rel.force_trivial_guard env0 g2;
                           if (FStar_List.length univs1) = Prims.int_zero
                           then generalize_and_inst_within env0 tcs datas1
                           else
                             (let uu____7137 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  tcs
                                 in
                              (uu____7137, datas1))
                            in
                         (match uu____7086 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____7169 =
                                  FStar_TypeChecker_Env.get_range env0  in
                                let uu____7170 =
                                  FStar_List.collect
                                    (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses
                                   in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____7169;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____7170;
                                  FStar_Syntax_Syntax.sigopts =
                                    FStar_Pervasives_Native.None
                                }  in
                              (FStar_All.pipe_right tcs1
                                 (FStar_List.iter
                                    (fun se  ->
                                       match se.FStar_Syntax_Syntax.sigel
                                       with
                                       | FStar_Syntax_Syntax.Sig_inductive_typ
                                           (l,univs2,binders,typ,uu____7196,uu____7197)
                                           ->
                                           let fail1 expected inferred =
                                             let uu____7217 =
                                               let uu____7223 =
                                                 let uu____7225 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     expected
                                                    in
                                                 let uu____7227 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     inferred
                                                    in
                                                 FStar_Util.format2
                                                   "Expected an inductive with type %s; got %s"
                                                   uu____7225 uu____7227
                                                  in
                                               (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                 uu____7223)
                                                in
                                             FStar_Errors.raise_error
                                               uu____7217
                                               se.FStar_Syntax_Syntax.sigrng
                                              in
                                           let uu____7231 =
                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                               env0 l
                                              in
                                           (match uu____7231 with
                                            | FStar_Pervasives_Native.None 
                                                -> ()
                                            | FStar_Pervasives_Native.Some
                                                (expected_typ1,uu____7247) ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu____7278 ->
                                                        let uu____7279 =
                                                          let uu____7280 =
                                                            let uu____7295 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                typ
                                                               in
                                                            (binders,
                                                              uu____7295)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_arrow
                                                            uu____7280
                                                           in
                                                        FStar_Syntax_Syntax.mk
                                                          uu____7279
                                                          se.FStar_Syntax_Syntax.sigrng
                                                     in
                                                  (univs2, body)  in
                                                if
                                                  (FStar_List.length univs2)
                                                    =
                                                    (FStar_List.length
                                                       (FStar_Pervasives_Native.fst
                                                          expected_typ1))
                                                then
                                                  let uu____7317 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      inferred_typ
                                                     in
                                                  (match uu____7317 with
                                                   | (uu____7322,inferred) ->
                                                       let uu____7324 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           expected_typ1
                                                          in
                                                       (match uu____7324 with
                                                        | (uu____7329,expected)
                                                            ->
                                                            let uu____7331 =
                                                              FStar_TypeChecker_Rel.teq_nosmt_force
                                                                env0 inferred
                                                                expected
                                                               in
                                                            if uu____7331
                                                            then ()
                                                            else
                                                              fail1
                                                                expected_typ1
                                                                inferred_typ))
                                                else
                                                  fail1 expected_typ1
                                                    inferred_typ)
                                       | uu____7338 -> ()));
                               (sig_bndle, tcs1, datas2))))))
  
let (early_prims_inductives : Prims.string Prims.list) =
  ["c_False"; "c_True"; "equals"; "h_equals"; "c_and"; "c_or"] 
let (mk_discriminator_and_indexed_projectors :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.fv_qual ->
        Prims.bool ->
          FStar_TypeChecker_Env.env ->
            FStar_Ident.lident ->
              FStar_Ident.lident ->
                FStar_Syntax_Syntax.univ_names ->
                  FStar_Syntax_Syntax.binders ->
                    FStar_Syntax_Syntax.binders ->
                      FStar_Syntax_Syntax.binders ->
                        Prims.bool -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun attrs  ->
      fun fvq  ->
        fun refine_domain  ->
          fun env  ->
            fun tc  ->
              fun lid  ->
                fun uvs  ->
                  fun inductive_tps  ->
                    fun indices  ->
                      fun fields  ->
                        fun erasable  ->
                          let p = FStar_Ident.range_of_lid lid  in
                          let pos q = FStar_Syntax_Syntax.withinfo q p  in
                          let projectee ptyp =
                            FStar_Syntax_Syntax.gen_bv "projectee"
                              (FStar_Pervasives_Native.Some p) ptyp
                             in
                          let inst_univs =
                            FStar_List.map
                              (fun u  -> FStar_Syntax_Syntax.U_name u) uvs
                             in
                          let tps = inductive_tps  in
                          let arg_typ =
                            let inst_tc =
                              let uu____7463 =
                                let uu____7464 =
                                  let uu____7471 =
                                    let uu____7474 =
                                      FStar_Syntax_Syntax.lid_as_fv tc
                                        FStar_Syntax_Syntax.delta_constant
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_Syntax_Syntax.fv_to_tm uu____7474
                                     in
                                  (uu____7471, inst_univs)  in
                                FStar_Syntax_Syntax.Tm_uinst uu____7464  in
                              FStar_Syntax_Syntax.mk uu____7463 p  in
                            let args =
                              FStar_All.pipe_right
                                (FStar_List.append tps indices)
                                (FStar_List.map
                                   (fun uu____7508  ->
                                      match uu____7508 with
                                      | (x,imp) ->
                                          let uu____7527 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7527, imp)))
                               in
                            FStar_Syntax_Syntax.mk_Tm_app inst_tc args p  in
                          let unrefined_arg_binder =
                            let uu____7531 = projectee arg_typ  in
                            FStar_Syntax_Syntax.mk_binder uu____7531  in
                          let arg_binder =
                            if Prims.op_Negation refine_domain
                            then unrefined_arg_binder
                            else
                              (let disc_name =
                                 FStar_Syntax_Util.mk_discriminator lid  in
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some p) arg_typ
                                  in
                               let sort =
                                 let disc_fvar =
                                   let uu____7554 =
                                     FStar_Ident.set_lid_range disc_name p
                                      in
                                   FStar_Syntax_Syntax.fvar uu____7554
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                     FStar_Pervasives_Native.None
                                    in
                                 let uu____7556 =
                                   let uu____7559 =
                                     let uu____7562 =
                                       FStar_Syntax_Syntax.mk_Tm_uinst
                                         disc_fvar inst_univs
                                        in
                                     let uu____7563 =
                                       let uu____7564 =
                                         let uu____7573 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7573
                                          in
                                       [uu____7564]  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____7562
                                       uu____7563 p
                                      in
                                   FStar_Syntax_Util.b2t uu____7559  in
                                 FStar_Syntax_Util.refine x uu____7556  in
                               let uu____7598 =
                                 let uu___1090_7599 = projectee arg_typ  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1090_7599.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1090_7599.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = sort
                                 }  in
                               FStar_Syntax_Syntax.mk_binder uu____7598)
                             in
                          let ntps = FStar_List.length tps  in
                          let all_params =
                            let uu____7616 =
                              FStar_List.map
                                (fun uu____7640  ->
                                   match uu____7640 with
                                   | (x,uu____7654) ->
                                       (x,
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.imp_tag)))
                                tps
                               in
                            FStar_List.append uu____7616 fields  in
                          let imp_binders =
                            FStar_All.pipe_right
                              (FStar_List.append tps indices)
                              (FStar_List.map
                                 (fun uu____7713  ->
                                    match uu____7713 with
                                    | (x,uu____7727) ->
                                        (x,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag))))
                             in
                          let early_prims_inductive =
                            (let uu____7738 =
                               FStar_TypeChecker_Env.current_module env  in
                             FStar_Ident.lid_equals
                               FStar_Parser_Const.prims_lid uu____7738)
                              &&
                              (FStar_List.existsb
                                 (fun s  ->
                                    s =
                                      (tc.FStar_Ident.ident).FStar_Ident.idText)
                                 early_prims_inductives)
                             in
                          let discriminator_ses =
                            if fvq <> FStar_Syntax_Syntax.Data_ctor
                            then []
                            else
                              (let discriminator_name =
                                 FStar_Syntax_Util.mk_discriminator lid  in
                               let no_decl = false  in
                               let only_decl =
                                 early_prims_inductive ||
                                   (let uu____7759 =
                                      let uu____7761 =
                                        FStar_TypeChecker_Env.current_module
                                          env
                                         in
                                      uu____7761.FStar_Ident.str  in
                                    FStar_Options.dont_gen_projectors
                                      uu____7759)
                                  in
                               let quals =
                                 let uu____7765 =
                                   FStar_List.filter
                                     (fun uu___4_7769  ->
                                        match uu___4_7769 with
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            Prims.op_Negation only_decl
                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                             -> true
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____7774 -> false) iquals
                                    in
                                 FStar_List.append
                                   ((FStar_Syntax_Syntax.Discriminator lid)
                                   ::
                                   (if only_decl
                                    then
                                      [FStar_Syntax_Syntax.Logic;
                                      FStar_Syntax_Syntax.Assumption]
                                    else [])) uu____7765
                                  in
                               let binders =
                                 FStar_List.append imp_binders
                                   [unrefined_arg_binder]
                                  in
                               let t =
                                 let bool_typ =
                                   if erasable
                                   then
                                     FStar_Syntax_Syntax.mk_GTotal
                                       FStar_Syntax_Util.t_bool
                                   else
                                     FStar_Syntax_Syntax.mk_Total
                                       FStar_Syntax_Util.t_bool
                                    in
                                 let uu____7819 =
                                   FStar_Syntax_Util.arrow binders bool_typ
                                    in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.close_univ_vars uvs)
                                   uu____7819
                                  in
                               let decl =
                                 let uu____7823 =
                                   FStar_Ident.range_of_lid
                                     discriminator_name
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_declare_typ
                                        (discriminator_name, uvs, t));
                                   FStar_Syntax_Syntax.sigrng = uu____7823;
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = attrs;
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 }  in
                               (let uu____7825 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "LogTypes")
                                   in
                                if uu____7825
                                then
                                  let uu____7829 =
                                    FStar_Syntax_Print.sigelt_to_string decl
                                     in
                                  FStar_Util.print1
                                    "Declaration of a discriminator %s\n"
                                    uu____7829
                                else ());
                               if only_decl
                               then [decl]
                               else
                                 (let body =
                                    if Prims.op_Negation refine_domain
                                    then FStar_Syntax_Util.exp_true_bool
                                    else
                                      (let arg_pats =
                                         FStar_All.pipe_right all_params
                                           (FStar_List.mapi
                                              (fun j  ->
                                                 fun uu____7890  ->
                                                   match uu____7890 with
                                                   | (x,imp) ->
                                                       let b =
                                                         FStar_Syntax_Syntax.is_implicit
                                                           imp
                                                          in
                                                       if b && (j < ntps)
                                                       then
                                                         let uu____7915 =
                                                           let uu____7918 =
                                                             let uu____7919 =
                                                               let uu____7926
                                                                 =
                                                                 FStar_Syntax_Syntax.gen_bv
                                                                   (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               (uu____7926,
                                                                 FStar_Syntax_Syntax.tun)
                                                                in
                                                             FStar_Syntax_Syntax.Pat_dot_term
                                                               uu____7919
                                                              in
                                                           pos uu____7918  in
                                                         (uu____7915, b)
                                                       else
                                                         (let uu____7934 =
                                                            let uu____7937 =
                                                              let uu____7938
                                                                =
                                                                FStar_Syntax_Syntax.gen_bv
                                                                  (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                  FStar_Pervasives_Native.None
                                                                  FStar_Syntax_Syntax.tun
                                                                 in
                                                              FStar_Syntax_Syntax.Pat_wild
                                                                uu____7938
                                                               in
                                                            pos uu____7937
                                                             in
                                                          (uu____7934, b))))
                                          in
                                       let pat_true =
                                         let uu____7957 =
                                           let uu____7960 =
                                             let uu____7961 =
                                               let uu____7975 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   lid
                                                   FStar_Syntax_Syntax.delta_constant
                                                   (FStar_Pervasives_Native.Some
                                                      fvq)
                                                  in
                                               (uu____7975, arg_pats)  in
                                             FStar_Syntax_Syntax.Pat_cons
                                               uu____7961
                                              in
                                           pos uu____7960  in
                                         (uu____7957,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_true_bool)
                                          in
                                       let pat_false =
                                         let uu____8010 =
                                           let uu____8013 =
                                             let uu____8014 =
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 FStar_Syntax_Syntax.tun
                                                in
                                             FStar_Syntax_Syntax.Pat_wild
                                               uu____8014
                                              in
                                           pos uu____8013  in
                                         (uu____8010,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_false_bool)
                                          in
                                       let arg_exp =
                                         FStar_Syntax_Syntax.bv_to_name
                                           (FStar_Pervasives_Native.fst
                                              unrefined_arg_binder)
                                          in
                                       let uu____8028 =
                                         let uu____8029 =
                                           let uu____8052 =
                                             let uu____8069 =
                                               FStar_Syntax_Util.branch
                                                 pat_true
                                                in
                                             let uu____8084 =
                                               let uu____8101 =
                                                 FStar_Syntax_Util.branch
                                                   pat_false
                                                  in
                                               [uu____8101]  in
                                             uu____8069 :: uu____8084  in
                                           (arg_exp, uu____8052)  in
                                         FStar_Syntax_Syntax.Tm_match
                                           uu____8029
                                          in
                                       FStar_Syntax_Syntax.mk uu____8028 p)
                                     in
                                  let dd =
                                    let uu____8177 =
                                      FStar_All.pipe_right quals
                                        (FStar_List.contains
                                           FStar_Syntax_Syntax.Abstract)
                                       in
                                    if uu____8177
                                    then
                                      FStar_Syntax_Syntax.Delta_abstract
                                        (FStar_Syntax_Syntax.Delta_equational_at_level
                                           Prims.int_one)
                                    else
                                      FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one
                                     in
                                  let imp =
                                    FStar_Syntax_Util.abs binders body
                                      FStar_Pervasives_Native.None
                                     in
                                  let lbtyp =
                                    if no_decl
                                    then t
                                    else FStar_Syntax_Syntax.tun  in
                                  let lb =
                                    let uu____8199 =
                                      let uu____8204 =
                                        FStar_Syntax_Syntax.lid_as_fv
                                          discriminator_name dd
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Util.Inr uu____8204  in
                                    let uu____8205 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        imp
                                       in
                                    FStar_Syntax_Util.mk_letbinding
                                      uu____8199 uvs lbtyp
                                      FStar_Parser_Const.effect_Tot_lid
                                      uu____8205 [] FStar_Range.dummyRange
                                     in
                                  let impl =
                                    let uu____8211 =
                                      let uu____8212 =
                                        let uu____8219 =
                                          let uu____8222 =
                                            let uu____8223 =
                                              FStar_All.pipe_right
                                                lb.FStar_Syntax_Syntax.lbname
                                                FStar_Util.right
                                               in
                                            FStar_All.pipe_right uu____8223
                                              (fun fv  ->
                                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                             in
                                          [uu____8222]  in
                                        ((false, [lb]), uu____8219)  in
                                      FStar_Syntax_Syntax.Sig_let uu____8212
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____8211;
                                      FStar_Syntax_Syntax.sigrng = p;
                                      FStar_Syntax_Syntax.sigquals = quals;
                                      FStar_Syntax_Syntax.sigmeta =
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs = attrs;
                                      FStar_Syntax_Syntax.sigopts =
                                        FStar_Pervasives_Native.None
                                    }  in
                                  (let uu____8237 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "LogTypes")
                                      in
                                   if uu____8237
                                   then
                                     let uu____8241 =
                                       FStar_Syntax_Print.sigelt_to_string
                                         impl
                                        in
                                     FStar_Util.print1
                                       "Implementation of a discriminator %s\n"
                                       uu____8241
                                   else ());
                                  [decl; impl]))
                             in
                          let arg_exp =
                            FStar_Syntax_Syntax.bv_to_name
                              (FStar_Pervasives_Native.fst arg_binder)
                             in
                          let binders =
                            FStar_List.append imp_binders [arg_binder]  in
                          let arg =
                            FStar_Syntax_Util.arg_of_non_null_binder
                              arg_binder
                             in
                          let subst1 =
                            FStar_All.pipe_right fields
                              (FStar_List.mapi
                                 (fun i  ->
                                    fun uu____8312  ->
                                      match uu____8312 with
                                      | (a,uu____8321) ->
                                          let field_name =
                                            FStar_Syntax_Util.mk_field_projector_name
                                              lid a i
                                             in
                                          let field_proj_tm =
                                            let uu____8328 =
                                              let uu____8329 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  field_name
                                                  (FStar_Syntax_Syntax.Delta_equational_at_level
                                                     Prims.int_one)
                                                  FStar_Pervasives_Native.None
                                                 in
                                              FStar_Syntax_Syntax.fv_to_tm
                                                uu____8329
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              uu____8328 inst_univs
                                             in
                                          let proj =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              field_proj_tm [arg] p
                                             in
                                          FStar_Syntax_Syntax.NT (a, proj)))
                             in
                          let projectors_ses =
                            let uu____8353 =
                              FStar_All.pipe_right fields
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____8393  ->
                                        match uu____8393 with
                                        | (x,uu____8404) ->
                                            let p1 =
                                              FStar_Syntax_Syntax.range_of_bv
                                                x
                                               in
                                            let field_name =
                                              FStar_Syntax_Util.mk_field_projector_name
                                                lid x i
                                               in
                                            let t =
                                              let result_comp =
                                                let t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    x.FStar_Syntax_Syntax.sort
                                                   in
                                                if erasable
                                                then
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                else
                                                  FStar_Syntax_Syntax.mk_Total
                                                    t
                                                 in
                                              let uu____8423 =
                                                FStar_Syntax_Util.arrow
                                                  binders result_comp
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Syntax_Subst.close_univ_vars
                                                   uvs) uu____8423
                                               in
                                            let only_decl =
                                              early_prims_inductive ||
                                                (let uu____8429 =
                                                   let uu____8431 =
                                                     FStar_TypeChecker_Env.current_module
                                                       env
                                                      in
                                                   uu____8431.FStar_Ident.str
                                                    in
                                                 FStar_Options.dont_gen_projectors
                                                   uu____8429)
                                               in
                                            let no_decl = false  in
                                            let quals q =
                                              if only_decl
                                              then
                                                let uu____8450 =
                                                  FStar_List.filter
                                                    (fun uu___5_8454  ->
                                                       match uu___5_8454 with
                                                       | FStar_Syntax_Syntax.Abstract
                                                            -> false
                                                       | uu____8457 -> true)
                                                    q
                                                   in
                                                FStar_Syntax_Syntax.Assumption
                                                  :: uu____8450
                                              else q  in
                                            let quals1 =
                                              let iquals1 =
                                                FStar_All.pipe_right iquals
                                                  (FStar_List.filter
                                                     (fun uu___6_8472  ->
                                                        match uu___6_8472
                                                        with
                                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                                             -> true
                                                        | FStar_Syntax_Syntax.NoExtract
                                                             -> true
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> true
                                                        | FStar_Syntax_Syntax.Private
                                                             -> true
                                                        | uu____8478 -> false))
                                                 in
                                              quals
                                                ((FStar_Syntax_Syntax.Projector
                                                    (lid,
                                                      (x.FStar_Syntax_Syntax.ppname)))
                                                :: iquals1)
                                               in
                                            let attrs1 =
                                              FStar_List.append
                                                (if only_decl
                                                 then []
                                                 else
                                                   [FStar_Syntax_Util.attr_substitute])
                                                attrs
                                               in
                                            let decl =
                                              let uu____8489 =
                                                FStar_Ident.range_of_lid
                                                  field_name
                                                 in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                                     (field_name, uvs, t));
                                                FStar_Syntax_Syntax.sigrng =
                                                  uu____8489;
                                                FStar_Syntax_Syntax.sigquals
                                                  = quals1;
                                                FStar_Syntax_Syntax.sigmeta =
                                                  FStar_Syntax_Syntax.default_sigmeta;
                                                FStar_Syntax_Syntax.sigattrs
                                                  = attrs1;
                                                FStar_Syntax_Syntax.sigopts =
                                                  FStar_Pervasives_Native.None
                                              }  in
                                            ((let uu____8491 =
                                                FStar_TypeChecker_Env.debug
                                                  env
                                                  (FStar_Options.Other
                                                     "LogTypes")
                                                 in
                                              if uu____8491
                                              then
                                                let uu____8495 =
                                                  FStar_Syntax_Print.sigelt_to_string
                                                    decl
                                                   in
                                                FStar_Util.print1
                                                  "Declaration of a projector %s\n"
                                                  uu____8495
                                              else ());
                                             if only_decl
                                             then [decl]
                                             else
                                               (let projection =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                    FStar_Pervasives_Native.None
                                                    FStar_Syntax_Syntax.tun
                                                   in
                                                let arg_pats =
                                                  FStar_All.pipe_right
                                                    all_params
                                                    (FStar_List.mapi
                                                       (fun j  ->
                                                          fun uu____8549  ->
                                                            match uu____8549
                                                            with
                                                            | (x1,imp) ->
                                                                let b =
                                                                  FStar_Syntax_Syntax.is_implicit
                                                                    imp
                                                                   in
                                                                if
                                                                  (i + ntps)
                                                                    = j
                                                                then
                                                                  let uu____8575
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                  (uu____8575,
                                                                    b)
                                                                else
                                                                  if
                                                                    b &&
                                                                    (j < ntps)
                                                                  then
                                                                    (
                                                                    let uu____8591
                                                                    =
                                                                    let uu____8594
                                                                    =
                                                                    let uu____8595
                                                                    =
                                                                    let uu____8602
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____8602,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8595
                                                                     in
                                                                    pos
                                                                    uu____8594
                                                                     in
                                                                    (uu____8591,
                                                                    b))
                                                                  else
                                                                    (
                                                                    let uu____8610
                                                                    =
                                                                    let uu____8613
                                                                    =
                                                                    let uu____8614
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8614
                                                                     in
                                                                    pos
                                                                    uu____8613
                                                                     in
                                                                    (uu____8610,
                                                                    b))))
                                                   in
                                                let pat =
                                                  let uu____8633 =
                                                    let uu____8636 =
                                                      let uu____8637 =
                                                        let uu____8651 =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            lid
                                                            FStar_Syntax_Syntax.delta_constant
                                                            (FStar_Pervasives_Native.Some
                                                               fvq)
                                                           in
                                                        (uu____8651,
                                                          arg_pats)
                                                         in
                                                      FStar_Syntax_Syntax.Pat_cons
                                                        uu____8637
                                                       in
                                                    pos uu____8636  in
                                                  let uu____8661 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      projection
                                                     in
                                                  (uu____8633,
                                                    FStar_Pervasives_Native.None,
                                                    uu____8661)
                                                   in
                                                let body =
                                                  let uu____8677 =
                                                    let uu____8678 =
                                                      let uu____8701 =
                                                        let uu____8718 =
                                                          FStar_Syntax_Util.branch
                                                            pat
                                                           in
                                                        [uu____8718]  in
                                                      (arg_exp, uu____8701)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_match
                                                      uu____8678
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____8677 p1
                                                   in
                                                let imp =
                                                  FStar_Syntax_Util.abs
                                                    binders body
                                                    FStar_Pervasives_Native.None
                                                   in
                                                let dd =
                                                  let uu____8783 =
                                                    FStar_All.pipe_right
                                                      quals1
                                                      (FStar_List.contains
                                                         FStar_Syntax_Syntax.Abstract)
                                                     in
                                                  if uu____8783
                                                  then
                                                    FStar_Syntax_Syntax.Delta_abstract
                                                      (FStar_Syntax_Syntax.Delta_equational_at_level
                                                         Prims.int_one)
                                                  else
                                                    FStar_Syntax_Syntax.Delta_equational_at_level
                                                      Prims.int_one
                                                   in
                                                let lbtyp =
                                                  if no_decl
                                                  then t
                                                  else
                                                    FStar_Syntax_Syntax.tun
                                                   in
                                                let lb =
                                                  let uu____8802 =
                                                    let uu____8807 =
                                                      FStar_Syntax_Syntax.lid_as_fv
                                                        field_name dd
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    FStar_Util.Inr uu____8807
                                                     in
                                                  let uu____8808 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs imp
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.lbname
                                                      = uu____8802;
                                                    FStar_Syntax_Syntax.lbunivs
                                                      = uvs;
                                                    FStar_Syntax_Syntax.lbtyp
                                                      = lbtyp;
                                                    FStar_Syntax_Syntax.lbeff
                                                      =
                                                      FStar_Parser_Const.effect_Tot_lid;
                                                    FStar_Syntax_Syntax.lbdef
                                                      = uu____8808;
                                                    FStar_Syntax_Syntax.lbattrs
                                                      = [];
                                                    FStar_Syntax_Syntax.lbpos
                                                      =
                                                      FStar_Range.dummyRange
                                                  }  in
                                                let impl =
                                                  let uu____8814 =
                                                    let uu____8815 =
                                                      let uu____8822 =
                                                        let uu____8825 =
                                                          let uu____8826 =
                                                            FStar_All.pipe_right
                                                              lb.FStar_Syntax_Syntax.lbname
                                                              FStar_Util.right
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____8826
                                                            (fun fv  ->
                                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                           in
                                                        [uu____8825]  in
                                                      ((false, [lb]),
                                                        uu____8822)
                                                       in
                                                    FStar_Syntax_Syntax.Sig_let
                                                      uu____8815
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.sigel
                                                      = uu____8814;
                                                    FStar_Syntax_Syntax.sigrng
                                                      = p1;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = quals1;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      =
                                                      FStar_Syntax_Syntax.default_sigmeta;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = attrs1;
                                                    FStar_Syntax_Syntax.sigopts
                                                      =
                                                      FStar_Pervasives_Native.None
                                                  }  in
                                                (let uu____8840 =
                                                   FStar_TypeChecker_Env.debug
                                                     env
                                                     (FStar_Options.Other
                                                        "LogTypes")
                                                    in
                                                 if uu____8840
                                                 then
                                                   let uu____8844 =
                                                     FStar_Syntax_Print.sigelt_to_string
                                                       impl
                                                      in
                                                   FStar_Util.print1
                                                     "Implementation of a projector %s\n"
                                                     uu____8844
                                                 else ());
                                                if no_decl
                                                then [impl]
                                                else [decl; impl]))))
                               in
                            FStar_All.pipe_right uu____8353
                              FStar_List.flatten
                             in
                          FStar_List.append discriminator_ses projectors_ses
  
let (mk_data_operations :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun attrs  ->
      fun env  ->
        fun tcs  ->
          fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_datacon
                (constr_lid,uvs,t,typ_lid,n_typars,uu____8907) when
                let uu____8914 =
                  FStar_Ident.lid_equals constr_lid
                    FStar_Parser_Const.lexcons_lid
                   in
                Prims.op_Negation uu____8914 ->
                let uu____8916 = FStar_Syntax_Subst.univ_var_opening uvs  in
                (match uu____8916 with
                 | (univ_opening,uvs1) ->
                     let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                     let uu____8938 = FStar_Syntax_Util.arrow_formals t1  in
                     (match uu____8938 with
                      | (formals,uu____8948) ->
                          let uu____8953 =
                            let tps_opt =
                              FStar_Util.find_map tcs
                                (fun se1  ->
                                   let uu____8988 =
                                     let uu____8990 =
                                       let uu____8991 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____8991  in
                                     FStar_Ident.lid_equals typ_lid
                                       uu____8990
                                      in
                                   if uu____8988
                                   then
                                     match se1.FStar_Syntax_Syntax.sigel with
                                     | FStar_Syntax_Syntax.Sig_inductive_typ
                                         (uu____9013,uvs',tps,typ0,uu____9017,constrs)
                                         ->
                                         FStar_Pervasives_Native.Some
                                           (tps, typ0,
                                             ((FStar_List.length constrs) >
                                                Prims.int_one))
                                     | uu____9037 -> failwith "Impossible"
                                   else FStar_Pervasives_Native.None)
                               in
                            match tps_opt with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                let uu____9086 =
                                  FStar_Ident.lid_equals typ_lid
                                    FStar_Parser_Const.exn_lid
                                   in
                                if uu____9086
                                then ([], FStar_Syntax_Util.ktype0, true)
                                else
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                      "Unexpected data constructor")
                                    se.FStar_Syntax_Syntax.sigrng
                             in
                          (match uu____8953 with
                           | (inductive_tps,typ0,should_refine) ->
                               let inductive_tps1 =
                                 FStar_Syntax_Subst.subst_binders
                                   univ_opening inductive_tps
                                  in
                               let typ01 =
                                 FStar_Syntax_Subst.subst univ_opening typ0
                                  in
                               let uu____9124 =
                                 FStar_Syntax_Util.arrow_formals typ01  in
                               (match uu____9124 with
                                | (indices,uu____9134) ->
                                    let refine_domain =
                                      let uu____9141 =
                                        FStar_All.pipe_right
                                          se.FStar_Syntax_Syntax.sigquals
                                          (FStar_Util.for_some
                                             (fun uu___7_9148  ->
                                                match uu___7_9148 with
                                                | FStar_Syntax_Syntax.RecordConstructor
                                                    uu____9150 -> true
                                                | uu____9160 -> false))
                                         in
                                      if uu____9141
                                      then false
                                      else should_refine  in
                                    let fv_qual =
                                      let filter_records uu___8_9175 =
                                        match uu___8_9175 with
                                        | FStar_Syntax_Syntax.RecordConstructor
                                            (uu____9178,fns) ->
                                            FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Syntax.Record_ctor
                                                 (constr_lid, fns))
                                        | uu____9190 ->
                                            FStar_Pervasives_Native.None
                                         in
                                      let uu____9191 =
                                        FStar_Util.find_map
                                          se.FStar_Syntax_Syntax.sigquals
                                          filter_records
                                         in
                                      match uu____9191 with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Syntax_Syntax.Data_ctor
                                      | FStar_Pervasives_Native.Some q -> q
                                       in
                                    let iquals1 =
                                      if
                                        (FStar_List.contains
                                           FStar_Syntax_Syntax.Abstract
                                           iquals)
                                          &&
                                          (Prims.op_Negation
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Private
                                                iquals))
                                      then FStar_Syntax_Syntax.Private ::
                                        iquals
                                      else iquals  in
                                    let fields =
                                      let uu____9204 =
                                        FStar_Util.first_N n_typars formals
                                         in
                                      match uu____9204 with
                                      | (imp_tps,fields) ->
                                          let rename =
                                            FStar_List.map2
                                              (fun uu____9287  ->
                                                 fun uu____9288  ->
                                                   match (uu____9287,
                                                           uu____9288)
                                                   with
                                                   | ((x,uu____9314),
                                                      (x',uu____9316)) ->
                                                       let uu____9337 =
                                                         let uu____9344 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x'
                                                            in
                                                         (x, uu____9344)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____9337) imp_tps
                                              inductive_tps1
                                             in
                                          FStar_Syntax_Subst.subst_binders
                                            rename fields
                                       in
                                    let erasable =
                                      FStar_Syntax_Util.has_attribute
                                        se.FStar_Syntax_Syntax.sigattrs
                                        FStar_Parser_Const.erasable_attr
                                       in
                                    mk_discriminator_and_indexed_projectors
                                      iquals1 attrs fv_qual refine_domain env
                                      typ_lid constr_lid uvs1 inductive_tps1
                                      indices fields erasable))))
            | uu____9351 -> []
  