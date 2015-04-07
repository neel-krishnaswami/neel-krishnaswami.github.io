
let map = lazyfix(function (map$42_2){
                    return function (st$46_3){
                      let f$47_4 = st$46_3();
                      return function (us$48_6){
                        let x$49_7 = us$48_6.head();
                        let xs$50_9 = us$48_6.tail();
                        return new Cons(f$47_4(x$49_7),
                                        new Lazy(function (){
                                                   let xs$50_15 = xs$50_9.force();
                                                   let map$42_17 = map$42_2.force();
                                                   return map$42_17(function (){
                                                                      return f$47_4;
                                                                    })(xs$50_15);
                                                 }));
                      };
                    };
                  });
let unfold = lazyfix(function (unfold$58_2){
                       return function (st$62_3){
                         let f$63_4 = st$62_3();
                         return function (seed$64_6){
                           let p$65_7 = f$63_4(seed$64_6);
                           let v$66_10 = p$65_7[0];
                           let d$67_12 = p$65_7[1];
                           let seed$68_14 = d$67_12;
                           return new Cons(v$66_10,
                                           new Lazy(function (){
                                                      let unfold$58_17 = unfold$58_2.force();
                                                      let seed$68_19 = seed$68_14.force();
                                                      return unfold$58_17(function (){
                                                                            return f$63_4;
                                                                          })(seed$68_19);
                                                    }));
                         };
                       };
                     });
let count = function (bs$72_2){
  return unfold(function (){
                  return function (u$80_6){
                    let n$81_7 = u$80_6[0];
                    let us$82_9 = u$80_6[1];
                    let b$83_11 = us$82_9.head();
                    let bs$84_13 = us$82_9.tail();
                    let m$85_15= null;
                    if (b$83_11) {
                      m$85_15 = n$81_7 + 1.;
                    } else {
                      m$85_15 = n$81_7;
                    }
                    return [m$85_15,
                            new Lazy(function (){
                                       let bs$84_21 = bs$84_13.force();
                                       return [m$85_15, bs$84_21];
                                     })];
                  };
                })([0., bs$72_2]);
};
let dynlabel = function (msgs$88_2){
  return function (){
    let update$109_3 = lazyfix(function (update$92_4){
                                 return function (i$96_5){
                                   let ss$97_6 = i$96_5;
                                   let s$98_7 = ss$97_6.head();
                                   let ss$99_9 = ss$97_6.tail();
                                   return function (w$100_11){
                                     let w$102_12 = text(s$98_7)()(w$100_11);
                                     let dom$103_18 = w$102_12;
                                     let w0$104_19 = dom$103_18;
                                     let w1$105_20 = new Lazy(function (){
                                                                return dom$103_18;
                                                              });
                                     return mergePrim(w0$104_19,
                                                      new Lazy(function (){
                                                                 let w1$105_23 = w1$105_20.force();
                                                                 let update$92_25 = update$92_4.force();
                                                                 let ss$99_27 = ss$99_9.force();
                                                                 return update$92_25(ss$99_27)(w1$105_23);
                                                               }));
                                   };
                                 };
                               });
    let w$111_33 = mkText("")();
    return update$109_3(msgs$88_2)(w$111_33);
  };
};
let main = function (){
  let w$120_2 = mkButton();
  let t$122_4 = clicks()(w$120_2);
  let w$123_8 = t$122_4[0];
  let i$124_10 = t$122_4[1];
  let bs$125_12 = i$124_10;
  let w0$138_13 = dynlabel(map(function (){
                                 return toString;
                               })(count(bs$125_12)))();
  return attach()([w$123_8, w0$138_13]);
};
let $main = function (){
  return main();
};
