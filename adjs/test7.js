
let choose = function (p$40_2){
  let e1$41_3 = p$40_2[0];
  let e2$42_5 = p$40_2[1];
  let e1$43_7 = e1$41_3;
  switch (e1$43_7[0]) {
    case "Nothing":
      let p$44_9 = e1$43_7[1];
      return e2$42_5;
    
    case "Digit":
      let n$45_10 = e1$43_7[1];
      return e1$43_7;
    
    case "Clear":
      let p$46_11 = e1$43_7[1];
      return e1$43_7;
    
    case "Push":
      let p$47_12 = e1$43_7[1];
      return e1$43_7;
    
    case "Pop":
      let p$48_13 = e1$43_7[1];
      return e1$43_7;
    
    case "BinOp":
      let f$49_14 = e1$43_7[1];
      return e1$43_7;
    
    case "UnOp":
      let f$50_15 = e1$43_7[1];
      return e1$43_7;
    }
};
let step = function (e$51_2){
  return function (stack$52_3){
    let pair$57_4 = [e$51_2, stack$52_3];
    let u$58_7 = pair$57_4;
    let event$59_8 = u$58_7[0];
    let list$61_10 = u$58_7[1];
    switch (event$59_8[0]) {
      case "Nothing":
        let p$60_13 = event$59_8[1];
        return stack$52_3;
      
      case "Digit":
        let n$62_14 = event$59_8[1];
        switch (list$61_10[0]) {
          case "Nil":
            let p$64_16 = list$61_10[1];
            return ["Cons", [n$62_14, ["Nil", []]]];
          
          case "Cons":
            let p$65_21 = list$61_10[1];
            let m$66_22 = p$65_21[0];
            let rest$67_24 = p$65_21[1];
            return ["Cons", [n$62_14 + 10. * m$66_22, rest$67_24]];
          }
      
      case "Clear":
        let p$68_33 = event$59_8[1];
        switch (list$61_10[0]) {
          case "Nil":
            let p$70_35 = list$61_10[1];
            return stack$52_3;
          
          case "Cons":
            let p$71_36 = list$61_10[1];
            let n$72_37 = p$71_36[0];
            let rest$73_39 = p$71_36[1];
            return ["Cons", [0., rest$73_39]];
          }
      
      case "Push":
        let p$74_44 = event$59_8[1];
        return ["Cons", [0., list$61_10]];
      
      case "Pop":
        let p$76_48 = event$59_8[1];
        switch (list$61_10[0]) {
          case "Nil":
            let p$78_50 = list$61_10[1];
            return stack$52_3;
          
          case "Cons":
            let p$79_51 = list$61_10[1];
            let n$80_52 = p$79_51[0];
            let rest$81_54 = p$79_51[1];
            return rest$81_54;
          }
      
      case "BinOp":
        let f$82_56 = event$59_8[1];
        switch (list$61_10[0]) {
          case "Nil":
            let p$84_58 = list$61_10[1];
            return stack$52_3;
          
          case "Cons":
            let p$85_59 = list$61_10[1];
            let n$86_60 = p$85_59[0];
            let list$87_62 = p$85_59[1];
            switch (list$87_62[0]) {
              case "Nil":
                let p$88_65 = list$87_62[1];
                return stack$52_3;
              
              case "Cons":
                let p$89_66 = list$87_62[1];
                let m$90_67 = p$89_66[0];
                let rest$91_69 = p$89_66[1];
                return ["Cons", [f$82_56(n$86_60)(m$90_67), rest$91_69]];
              }
          }
      
      case "UnOp":
        let f$92_78 = event$59_8[1];
        switch (list$61_10[0]) {
          case "Nil":
            let p$94_80 = list$61_10[1];
            return stack$52_3;
          
          case "Cons":
            let p$95_81 = list$61_10[1];
            let n$96_82 = p$95_81[0];
            let rest$97_84 = p$95_81[1];
            return ["Cons", [f$92_78(n$96_82), rest$97_84]];
          }
      }
  };
};
let states = lazyfix(function (states$98_2){
                       return function (qs$100_3){
                         let u$101_4 = qs$100_3.head();
                         let us$102_6 = qs$100_3.tail();
                         return function (state$103_8){
                           return function (events$104_9){
                             let e$105_10 = events$104_9.head();
                             let es$106_12 = events$104_9.tail();
                             let u$111_14 = step(e$105_10)(state$103_8);
                             let state$112_19 = u$111_14;
                             return new Cons(state$112_19,
                                             new Lazy(function (){
                                                        let us$102_22 = us$102_6.force();
                                                        let states$98_24 = states$98_2.force();
                                                        let es$106_26 = es$106_12.force();
                                                        return states$98_24(us$102_22)(state$112_19)(es$106_26);
                                                      }));
                           };
                         };
                       };
                     });
let ints = lazyfix(function (ints$113_2){
                     return function (qs$115_3){
                       let u$116_4 = qs$115_3.head();
                       let us$117_6 = qs$115_3.tail();
                       return function (n$118_8){
                         return new Cons(n$118_8,
                                         new Lazy(function (){
                                                    let us$117_11 = us$117_6.force();
                                                    let ints$113_13 = ints$113_2.force();
                                                    return ints$113_13(us$117_11)(n$118_8 + 1.);
                                                  }));
                       };
                     };
                   });
let stackToString = function stackToString$119_2(ns$120_3){
  while (true) {
    let ns$120_4 = ns$120_3;
    let list$121_5 = ns$120_4;
    switch (list$121_5[0]) {
      case "Nil":
        let p$122_7 = list$121_5[1];
        return "--";
      
      case "Cons":
        let p$123_8 = list$121_5[1];
        let n$124_9 = p$123_8[0];
        let xs$125_11 = p$123_8[1];
        switch (xs$125_11[0]) {
          case "Nil":
            let p$126_14 = xs$125_11[1];
            return toString(n$124_9);
          
          case "Cons":
            let p$127_17 = xs$125_11[1];
            let m$128_18 = n$124_9;
            return cat([toString(m$128_18), cat(["  ", stackToString$119_2(xs$125_11)])]);
          }
      }
  }
};
let map = lazyfix(function (map$139_2){
                    return function (st$149_3){
                      let f$150_4 = st$149_3;
                      return function (qs$151_5){
                        let u$152_6 = qs$151_5.head();
                        let us$153_8 = qs$151_5.tail();
                        return function (us$154_10){
                          let x$155_11 = us$154_10.head();
                          let xs$156_13 = us$154_10.tail();
                          return new Cons(f$150_4(x$155_11),
                                          new Lazy(function (){
                                                     let xs$156_19 = xs$156_13.force();
                                                     let us$153_21 = us$153_8.force();
                                                     let map$139_23 = map$139_2.force();
                                                     return map$139_23(f$150_4)(us$153_21)(xs$156_19);
                                                   }));
                        };
                      };
                    };
                  });
let zip = lazyfix(function (zip$179_2){
                    return function (qs$189_3){
                      let u$190_4 = qs$189_3.head();
                      let us$191_6 = qs$189_3.tail();
                      return function (us$192_8){
                        let a$193_9 = us$192_8.head();
                        let as$194_11 = us$192_8.tail();
                        return function (us$195_13){
                          let b$196_14 = us$195_13.head();
                          let bs$197_16 = us$195_13.tail();
                          return new Cons([a$193_9, b$196_14],
                                          new Lazy(function (){
                                                     let zip$179_22 = zip$179_2.force();
                                                     let us$191_24 = us$191_6.force();
                                                     let bs$197_26 = bs$197_16.force();
                                                     let as$194_28 = as$194_11.force();
                                                     return zip$179_22(us$191_24)(as$194_28)(bs$197_26);
                                                   }));
                        };
                      };
                    };
                  });
let unfold = lazyfix(function (unfold$219_2){
                       return function (st$229_3){
                         let f$230_4 = st$229_3;
                         return function (qs$231_5){
                           let u$232_6 = qs$231_5.head();
                           let us$233_8 = qs$231_5.tail();
                           return function (seed$234_10){
                             let p$235_11 = f$230_4(u$232_6)(seed$234_10);
                             let b$236_16 = p$235_11[0];
                             let d$237_18 = p$235_11[1];
                             let seed$238_20 = d$237_18;
                             return new Cons(b$236_16,
                                             new Lazy(function (){
                                                        let us$233_23 = us$233_8.force();
                                                        let unfold$219_25 = unfold$219_2.force();
                                                        let seed$238_27 = seed$238_20.force();
                                                        return unfold$219_25(f$230_4)(us$233_23)(seed$238_27);
                                                      }));
                           };
                         };
                       };
                     });
let mux = function (us$251_2){
  return function (es1$252_3){
    return function (es2$253_4){
      return map(choose)(us$251_2)(zip(us$251_2)(es1$252_3)(es2$253_4));
    };
  };
};
let button = function (us$289_2){
  return function (label$293_3){
    return function (e$297_4){
      return function (){
        let w$309_5 = mkButton();
        let w$323_7 = text(label$293_3)()(w$309_5);
        let w$341_13 = width("4em")()(w$323_7);
        let t$363_19 = clicks(us$289_2)()(w$341_13);
        let w$364_25 = t$363_19[0];
        let i$365_27 = t$363_19[1];
        let bs$366_29 = i$365_27;
        return [w$364_25,
                map(function (b$411_36){
                      if (b$411_36) {
                        return e$297_4;
                      } else {
                        return ["Nothing", []];
                      }
                    })(us$289_2)(bs$366_29)];
      };
    };
  };
};
let numeric = function (us$413_2){
  return function (n$417_3){
    return button(us$413_2)(toString(n$417_3))(["Digit", n$417_3]);
  };
};
let panel = function (us$454_2){
  return function (mkBox$473_3){
    return function (p$489_4){
      let b1$502_5 = p$489_4[0];
      let b2$503_7 = p$489_4[1];
      let b3$504_9 = p$489_4[2];
      let b4$505_11 = p$489_4[3];
      return function (){
        let box$517_13 = mkBox$473_3();
        let t$524_15 = b1$502_5();
        let w1$526_17 = t$524_15[0];
        let i$527_19 = t$524_15[1];
        let es1$528_21 = i$527_19;
        let t$535_22 = b2$503_7();
        let w2$537_24 = t$535_22[0];
        let i$538_26 = t$535_22[1];
        let es2$539_28 = i$538_26;
        let t$546_29 = b3$504_9();
        let w3$548_31 = t$546_29[0];
        let i$549_33 = t$546_29[1];
        let es3$550_35 = i$549_33;
        let t$557_36 = b4$505_11();
        let w4$559_38 = t$557_36[0];
        let i$560_40 = t$557_36[1];
        let es4$561_42 = i$560_40;
        let box$582_43 = attach()([box$517_13, w1$526_17]);
        let box$615_49 = attach()([box$582_43, w2$537_24]);
        let box$660_55 = attach()([box$615_49, w3$548_31]);
        let box$717_61 = attach()([box$660_55, w4$559_38]);
        return [box$717_61, mux(us$454_2)(es1$528_21)(mux(us$454_2)(es2$539_28)(mux(us$454_2)(es3$550_35)(es4$561_42)))];
      };
    };
  };
};
let inputPanel = function (us$754_2){
  return panel(us$754_2)(vbox)([panel(us$754_2)(hbox)([numeric(us$754_2)(7.),
                                                       numeric(us$754_2)(8.),
                                                       numeric(us$754_2)(9.),
                                                       button(us$754_2)("x")(["BinOp",
                                                                              function (a$988_39){
                                                                                return function (b$989_40){
                                                                                  return a$988_39 * b$989_40;
                                                                                };
                                                                              }])]),
                                panel(us$754_2)(hbox)([numeric(us$754_2)(4.),
                                                       numeric(us$754_2)(5.),
                                                       numeric(us$754_2)(6.),
                                                       button(us$754_2)("+")(["BinOp",
                                                                              function (a$1192_73){
                                                                                return function (b$1193_74){
                                                                                  return a$1192_73 + b$1193_74;
                                                                                };
                                                                              }])]),
                                panel(us$754_2)(hbox)([numeric(us$754_2)(1.), numeric(us$754_2)(2.), numeric(us$754_2)(3.), button(us$754_2)("Pop")(["Pop", []])]),
                                panel(us$754_2)(hbox)([button(us$754_2)("+/-")(["UnOp",
                                                                                function (n$1517_122){
                                                                                  return 0. - n$1517_122;
                                                                                }]),
                                                       numeric(us$754_2)(0.),
                                                       button(us$754_2)("C")(["Clear", []]),
                                                       button(us$754_2)("Push")(["Push", []])])]);
};
let dynlabel = function (us$1666_2){
  return function (ss$1670_3){
    return function (){
      let displayText$1743_4 = lazyfix(function (displayText$1683_5){
                                         return function (i$1690_6){
                                           let qs$1691_7 = i$1690_6;
                                           let u$1692_8 = qs$1691_7.head();
                                           let us$1693_10 = qs$1691_7.tail();
                                           return function (i$1694_12){
                                             let ss$1695_13 = i$1694_12;
                                             let s$1696_14 = ss$1695_13.head();
                                             let ss$1697_16 = ss$1695_13.tail();
                                             return function (w$1698_18){
                                               let w$1709_19 = text(s$1696_14)()(w$1698_18);
                                               let t$1719_25 = split()(w$1709_19);
                                               let w0$1720_29 = t$1719_25[0];
                                               let d$1721_31 = t$1719_25[1];
                                               let w1$1722_33 = d$1721_31;
                                               return merge()([w0$1720_29,
                                                               new Lazy(function (){
                                                                          let w1$1722_39 = w1$1722_33.force();
                                                                          let us$1693_41 = us$1693_10.force();
                                                                          let ss$1697_43 = ss$1697_16.force();
                                                                          let displayText$1683_45 = displayText$1683_5.force();
                                                                          return displayText$1683_45(us$1693_41)(ss$1697_43)(w1$1722_39);
                                                                        })]);
                                             };
                                           };
                                         };
                                       });
      let w$1754_53 = mkText("")();
      return displayText$1743_4(us$1666_2)(ss$1670_3)(w$1754_53);
    };
  };
};
let main = function (us$1770_2){
  return function (){
    let t$1782_3 = inputPanel(us$1770_2)();
    let wpanel$1784_7 = t$1782_3[0];
    let i$1785_9 = t$1782_3[1];
    let events$1786_11 = i$1785_9;
    let events$1791_14 = states(us$1770_2)(["Nil", []])(events$1786_11);
    let labels$1808_22 = map(stackToString)(us$1770_2)(events$1791_14);
    let wdisplay$1850_12 = dynlabel(us$1770_2)(labels$1808_22)();
    let wdisplay$1864_33 = backgroundColor("rgb(60,60,60)")()(wdisplay$1850_12);
    let wdisplay$1882_39 = fontFamily("monospace")()(wdisplay$1864_33);
    let box$1894_45 = vbox();
    let box$1927_47 = attach()([box$1894_45, wdisplay$1882_39]);
    let box$1972_53 = attach()([box$1927_47, wpanel$1784_7]);
    return box$1972_53;
  };
};
let $main = function ($alloc){
  return main($alloc);
};
