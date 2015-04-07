
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
                       return function (state$100_3){
                         return function (events$101_4){
                           let e$102_5 = events$101_4.head();
                           let es$103_7 = events$101_4.tail();
                           let u$108_9 = function (){
                             return step(e$102_5)(state$100_3);
                           };
                           let state$109_14 = u$108_9();
                           return new Cons(state$109_14,
                                           new Lazy(function (){
                                                      let states$98_18 = states$98_2.force();
                                                      let es$103_20 = es$103_7.force();
                                                      return states$98_18(state$109_14)(es$103_20);
                                                    }));
                         };
                       };
                     });
let ints = lazyfix(function (ints$110_2){
                     return function (n$112_3){
                       return new Cons(n$112_3,
                                       new Lazy(function (){
                                                  let ints$110_6 = ints$110_2.force();
                                                  return ints$110_6(n$112_3 + 1.);
                                                }));
                     };
                   });
let stackToString = function stackToString$113_2(ns$114_3){
  while (true) {
    let ns$114_4 = ns$114_3;
    let list$115_5 = ns$114_4;
    switch (list$115_5[0]) {
      case "Nil":
        let p$116_7 = list$115_5[1];
        return "--";
      
      case "Cons":
        let p$117_8 = list$115_5[1];
        let n$118_9 = p$117_8[0];
        let xs$119_11 = p$117_8[1];
        switch (xs$119_11[0]) {
          case "Nil":
            let p$120_14 = xs$119_11[1];
            return toString(n$118_9);
          
          case "Cons":
            let p$121_17 = xs$119_11[1];
            let m$122_18 = n$118_9;
            return cat([toString(m$122_18), cat(["  ", stackToString$113_2(xs$119_11)])]);
          }
      }
  }
};
let map = lazyfix(function (map$133_2){
                    return function (st$143_3){
                      let f$144_4 = st$143_3();
                      return function (us$145_6){
                        let x$146_7 = us$145_6.head();
                        let xs$147_9 = us$145_6.tail();
                        return new Cons(f$144_4(x$146_7),
                                        new Lazy(function (){
                                                   let xs$147_15 = xs$147_9.force();
                                                   let map$133_17 = map$133_2.force();
                                                   return map$133_17(function (){
                                                                       return f$144_4;
                                                                     })(xs$147_15);
                                                 }));
                      };
                    };
                  });
let zip = lazyfix(function (zip$170_2){
                    return function (us$180_3){
                      let a$181_4 = us$180_3.head();
                      let as$182_6 = us$180_3.tail();
                      return function (us$183_8){
                        let b$184_9 = us$183_8.head();
                        let bs$185_11 = us$183_8.tail();
                        return new Cons([a$181_4, b$184_9],
                                        new Lazy(function (){
                                                   let zip$170_17 = zip$170_2.force();
                                                   let bs$185_19 = bs$185_11.force();
                                                   let as$182_21 = as$182_6.force();
                                                   return zip$170_17(as$182_21)(bs$185_19);
                                                 }));
                      };
                    };
                  });
let unfold = lazyfix(function (unfold$207_2){
                       return function (st$217_3){
                         let f$218_4 = st$217_3();
                         return function (seed$219_6){
                           let p$220_7 = f$218_4(seed$219_6);
                           let b$221_10 = p$220_7[0];
                           let d$222_12 = p$220_7[1];
                           let seed$223_14 = d$222_12;
                           return new Cons(b$221_10,
                                           new Lazy(function (){
                                                      let unfold$207_17 = unfold$207_2.force();
                                                      let seed$223_19 = seed$223_14.force();
                                                      return unfold$207_17(function (){
                                                                             return f$218_4;
                                                                           })(seed$223_19);
                                                    }));
                         };
                       };
                     });
let mux = function (es1$236_2){
  return function (es2$237_3){
    return map(function (){
                 return choose;
               })(zip(es1$236_2)(es2$237_3));
  };
};
let button = function (label$273_2){
  return function (e$277_3){
    return function (){
      let w$289_4 = mkButton();
      let w$303_6 = text(label$273_2)()(w$289_4);
      let w$321_12 = width("4em")()(w$303_6);
      let t$338_18 = clicks()(w$321_12);
      let w$339_22 = t$338_18[0];
      let i$340_24 = t$338_18[1];
      let bs$341_26 = i$340_24;
      return [w$339_22,
              map(function (){
                    return function (b$386_32){
                      if (b$386_32) {
                        return e$277_3;
                      } else {
                        return ["Nothing", []];
                      }
                    };
                  })(bs$341_26)];
    };
  };
};
let numeric = function (n$388_2){
  return button(toString(n$388_2))(["Digit", n$388_2]);
};
let panel = function (mkBox$422_2){
  return function (p$438_3){
    let b1$451_4 = p$438_3[0];
    let b2$452_6 = p$438_3[1];
    let b3$453_8 = p$438_3[2];
    let b4$454_10 = p$438_3[3];
    return function (){
      let box$466_12 = mkBox$422_2();
      let t$473_14 = b1$451_4();
      let w1$475_16 = t$473_14[0];
      let i$476_18 = t$473_14[1];
      let es1$477_20 = i$476_18;
      let t$484_21 = b2$452_6();
      let w2$486_23 = t$484_21[0];
      let i$487_25 = t$484_21[1];
      let es2$488_27 = i$487_25;
      let t$495_28 = b3$453_8();
      let w3$497_30 = t$495_28[0];
      let i$498_32 = t$495_28[1];
      let es3$499_34 = i$498_32;
      let t$506_35 = b4$454_10();
      let w4$508_37 = t$506_35[0];
      let i$509_39 = t$506_35[1];
      let es4$510_41 = i$509_39;
      let box$531_42 = attach()([box$466_12, w1$475_16]);
      let box$564_48 = attach()([box$531_42, w2$486_23]);
      let box$609_54 = attach()([box$564_48, w3$497_30]);
      let box$666_60 = attach()([box$609_54, w4$508_37]);
      return [box$666_60, mux(es1$477_20)(mux(es2$488_27)(mux(es3$499_34)(es4$510_41)))];
    };
  };
};
let inputPanel = panel(vbox)([panel(hbox)([numeric(7.),
                                           numeric(8.),
                                           numeric(9.),
                                           button("x")(["BinOp",
                                                        function (a$885_26){
                                                          return function (b$886_27){
                                                            return a$885_26 * b$886_27;
                                                          };
                                                        }])]),
                              panel(hbox)([numeric(4.),
                                           numeric(5.),
                                           numeric(6.),
                                           button("+")(["BinOp",
                                                        function (a$1059_50){
                                                          return function (b$1060_51){
                                                            return a$1059_50 + b$1060_51;
                                                          };
                                                        }])]),
                              panel(hbox)([numeric(1.), numeric(2.), numeric(3.), button("Pop")(["Pop", []])]),
                              panel(hbox)([button("+/-")(["UnOp",
                                                          function (n$1333_85){
                                                            return 0. - n$1333_85;
                                                          }]),
                                           numeric(0.),
                                           button("C")(["Clear", []]),
                                           button("Push")(["Push", []])])]);
let dynlabel = function (ss$1473_2){
  return function (){
    let displayText$1541_3 = lazyfix(function (displayText$1486_4){
                                       return function (i$1493_5){
                                         let ss$1494_6 = i$1493_5;
                                         let s$1495_7 = ss$1494_6.head();
                                         let ss$1496_9 = ss$1494_6.tail();
                                         return function (w$1497_11){
                                           let w$1508_12 = text(s$1495_7)()(w$1497_11);
                                           let t$1518_18 = split()(w$1508_12);
                                           let w0$1519_22 = t$1518_18[0];
                                           let d$1520_24 = t$1518_18[1];
                                           let w1$1521_26 = d$1520_24;
                                           return merge()([w0$1519_22,
                                                           new Lazy(function (){
                                                                      let w1$1521_32 = w1$1521_26.force();
                                                                      let ss$1496_34 = ss$1496_9.force();
                                                                      let displayText$1486_36 = displayText$1486_4.force();
                                                                      return displayText$1486_36(ss$1496_34)(w1$1521_32);
                                                                    })]);
                                         };
                                       };
                                     });
    let w$1552_42 = mkText("")();
    return displayText$1541_3(ss$1473_2)(w$1552_42);
  };
};
let main = function (){
  let t$1572_2 = inputPanel();
  let wpanel$1574_4 = t$1572_2[0];
  let i$1575_6 = t$1572_2[1];
  let events$1576_8 = i$1575_6;
  let events$1581_11 = states(["Nil", []])(events$1576_8);
  let labels$1598_17 = map(function (){
                             return stackToString;
                           })(events$1581_11);
  let wdisplay$1634_9 = dynlabel(labels$1598_17)();
  let wdisplay$1648_24 = backgroundColor("rgb(60,60,60)")()(wdisplay$1634_9);
  let wdisplay$1666_30 = fontFamily("monospace")()(wdisplay$1648_24);
  let box$1678_36 = vbox();
  let box$1711_38 = attach()([box$1678_36, wdisplay$1666_30]);
  let box$1756_44 = attach()([box$1711_38, wpanel$1574_4]);
  return box$1756_44;
};
let $main = function (){
  return main();
};
