src/b1.vo src/b1.glob src/b1.v.beautified src/b1.required_vo: src/b1.v 
src/b1.vio: src/b1.v 
src/b1.vos src/b1.vok src/b1.required_vos: src/b1.v 
src/b2.vo src/b2.glob src/b2.v.beautified src/b2.required_vo: src/b2.v src/b1.vo
src/b2.vio: src/b2.v src/b1.vio
src/b2.vos src/b2.vok src/b2.required_vos: src/b2.v src/b1.vos
src/b3.vo src/b3.glob src/b3.v.beautified src/b3.required_vo: src/b3.v src/b1.vo src/b2.vo
src/b3.vio: src/b3.v src/b1.vio src/b2.vio
src/b3.vos src/b3.vok src/b3.required_vos: src/b3.v src/b1.vos src/b2.vos
