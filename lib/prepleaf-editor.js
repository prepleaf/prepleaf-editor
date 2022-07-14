'use strict';

var React = require('react');
var Draft = require('draft-js');
var katex$1 = require('katex');

function _interopDefaultLegacy (e) { return e && typeof e === 'object' && 'default' in e ? e : { 'default': e }; }

var React__default = /*#__PURE__*/_interopDefaultLegacy(React);
var Draft__default = /*#__PURE__*/_interopDefaultLegacy(Draft);
var katex__default = /*#__PURE__*/_interopDefaultLegacy(katex$1);

function ownKeys(object, enumerableOnly) {
  var keys = Object.keys(object);

  if (Object.getOwnPropertySymbols) {
    var symbols = Object.getOwnPropertySymbols(object);
    enumerableOnly && (symbols = symbols.filter(function (sym) {
      return Object.getOwnPropertyDescriptor(object, sym).enumerable;
    })), keys.push.apply(keys, symbols);
  }

  return keys;
}

function _objectSpread2(target) {
  for (var i = 1; i < arguments.length; i++) {
    var source = null != arguments[i] ? arguments[i] : {};
    i % 2 ? ownKeys(Object(source), !0).forEach(function (key) {
      _defineProperty(target, key, source[key]);
    }) : Object.getOwnPropertyDescriptors ? Object.defineProperties(target, Object.getOwnPropertyDescriptors(source)) : ownKeys(Object(source)).forEach(function (key) {
      Object.defineProperty(target, key, Object.getOwnPropertyDescriptor(source, key));
    });
  }

  return target;
}

function _typeof(obj) {
  "@babel/helpers - typeof";

  return _typeof = "function" == typeof Symbol && "symbol" == typeof Symbol.iterator ? function (obj) {
    return typeof obj;
  } : function (obj) {
    return obj && "function" == typeof Symbol && obj.constructor === Symbol && obj !== Symbol.prototype ? "symbol" : typeof obj;
  }, _typeof(obj);
}

function _classCallCheck(instance, Constructor) {
  if (!(instance instanceof Constructor)) {
    throw new TypeError("Cannot call a class as a function");
  }
}

function _defineProperties(target, props) {
  for (var i = 0; i < props.length; i++) {
    var descriptor = props[i];
    descriptor.enumerable = descriptor.enumerable || false;
    descriptor.configurable = true;
    if ("value" in descriptor) descriptor.writable = true;
    Object.defineProperty(target, descriptor.key, descriptor);
  }
}

function _createClass(Constructor, protoProps, staticProps) {
  if (protoProps) _defineProperties(Constructor.prototype, protoProps);
  if (staticProps) _defineProperties(Constructor, staticProps);
  Object.defineProperty(Constructor, "prototype", {
    writable: false
  });
  return Constructor;
}

function _defineProperty(obj, key, value) {
  if (key in obj) {
    Object.defineProperty(obj, key, {
      value: value,
      enumerable: true,
      configurable: true,
      writable: true
    });
  } else {
    obj[key] = value;
  }

  return obj;
}

function _extends() {
  _extends = Object.assign ? Object.assign.bind() : function (target) {
    for (var i = 1; i < arguments.length; i++) {
      var source = arguments[i];

      for (var key in source) {
        if (Object.prototype.hasOwnProperty.call(source, key)) {
          target[key] = source[key];
        }
      }
    }

    return target;
  };
  return _extends.apply(this, arguments);
}

function _inherits(subClass, superClass) {
  if (typeof superClass !== "function" && superClass !== null) {
    throw new TypeError("Super expression must either be null or a function");
  }

  subClass.prototype = Object.create(superClass && superClass.prototype, {
    constructor: {
      value: subClass,
      writable: true,
      configurable: true
    }
  });
  Object.defineProperty(subClass, "prototype", {
    writable: false
  });
  if (superClass) _setPrototypeOf(subClass, superClass);
}

function _getPrototypeOf(o) {
  _getPrototypeOf = Object.setPrototypeOf ? Object.getPrototypeOf.bind() : function _getPrototypeOf(o) {
    return o.__proto__ || Object.getPrototypeOf(o);
  };
  return _getPrototypeOf(o);
}

function _setPrototypeOf(o, p) {
  _setPrototypeOf = Object.setPrototypeOf ? Object.setPrototypeOf.bind() : function _setPrototypeOf(o, p) {
    o.__proto__ = p;
    return o;
  };
  return _setPrototypeOf(o, p);
}

function _isNativeReflectConstruct() {
  if (typeof Reflect === "undefined" || !Reflect.construct) return false;
  if (Reflect.construct.sham) return false;
  if (typeof Proxy === "function") return true;

  try {
    Boolean.prototype.valueOf.call(Reflect.construct(Boolean, [], function () {}));
    return true;
  } catch (e) {
    return false;
  }
}

function _assertThisInitialized(self) {
  if (self === void 0) {
    throw new ReferenceError("this hasn't been initialised - super() hasn't been called");
  }

  return self;
}

function _possibleConstructorReturn(self, call) {
  if (call && (typeof call === "object" || typeof call === "function")) {
    return call;
  } else if (call !== void 0) {
    throw new TypeError("Derived constructors may only return object or undefined");
  }

  return _assertThisInitialized(self);
}

function _createSuper(Derived) {
  var hasNativeReflectConstruct = _isNativeReflectConstruct();

  return function _createSuperInternal() {
    var Super = _getPrototypeOf(Derived),
        result;

    if (hasNativeReflectConstruct) {
      var NewTarget = _getPrototypeOf(this).constructor;

      result = Reflect.construct(Super, arguments, NewTarget);
    } else {
      result = Super.apply(this, arguments);
    }

    return _possibleConstructorReturn(this, result);
  };
}

var commonjsGlobal = typeof globalThis !== 'undefined' ? globalThis : typeof window !== 'undefined' ? window : typeof global !== 'undefined' ? global : typeof self !== 'undefined' ? self : {};

function createCommonjsModule(fn, module) {
	return module = { exports: {} }, fn(module, module.exports), module.exports;
}

/** @license React v16.13.1
 * react-is.production.min.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */
var b="function"===typeof Symbol&&Symbol.for,c=b?Symbol.for("react.element"):60103,d=b?Symbol.for("react.portal"):60106,e=b?Symbol.for("react.fragment"):60107,f=b?Symbol.for("react.strict_mode"):60108,g=b?Symbol.for("react.profiler"):60114,h=b?Symbol.for("react.provider"):60109,k=b?Symbol.for("react.context"):60110,l=b?Symbol.for("react.async_mode"):60111,m=b?Symbol.for("react.concurrent_mode"):60111,n=b?Symbol.for("react.forward_ref"):60112,p=b?Symbol.for("react.suspense"):60113,q=b?
Symbol.for("react.suspense_list"):60120,r=b?Symbol.for("react.memo"):60115,t=b?Symbol.for("react.lazy"):60116,v=b?Symbol.for("react.block"):60121,w=b?Symbol.for("react.fundamental"):60117,x=b?Symbol.for("react.responder"):60118,y=b?Symbol.for("react.scope"):60119;
function z(a){if("object"===typeof a&&null!==a){var u=a.$$typeof;switch(u){case c:switch(a=a.type,a){case l:case m:case e:case g:case f:case p:return a;default:switch(a=a&&a.$$typeof,a){case k:case n:case t:case r:case h:return a;default:return u}}case d:return u}}}function A(a){return z(a)===m}var AsyncMode=l;var ConcurrentMode=m;var ContextConsumer=k;var ContextProvider=h;var Element=c;var ForwardRef=n;var Fragment=e;var Lazy=t;var Memo=r;var Portal=d;
var Profiler=g;var StrictMode=f;var Suspense=p;var isAsyncMode=function(a){return A(a)||z(a)===l};var isConcurrentMode=A;var isContextConsumer=function(a){return z(a)===k};var isContextProvider=function(a){return z(a)===h};var isElement=function(a){return "object"===typeof a&&null!==a&&a.$$typeof===c};var isForwardRef=function(a){return z(a)===n};var isFragment=function(a){return z(a)===e};var isLazy=function(a){return z(a)===t};
var isMemo=function(a){return z(a)===r};var isPortal=function(a){return z(a)===d};var isProfiler=function(a){return z(a)===g};var isStrictMode=function(a){return z(a)===f};var isSuspense=function(a){return z(a)===p};
var isValidElementType=function(a){return "string"===typeof a||"function"===typeof a||a===e||a===m||a===g||a===f||a===p||a===q||"object"===typeof a&&null!==a&&(a.$$typeof===t||a.$$typeof===r||a.$$typeof===h||a.$$typeof===k||a.$$typeof===n||a.$$typeof===w||a.$$typeof===x||a.$$typeof===y||a.$$typeof===v)};var typeOf=z;

var reactIs_production_min = {
	AsyncMode: AsyncMode,
	ConcurrentMode: ConcurrentMode,
	ContextConsumer: ContextConsumer,
	ContextProvider: ContextProvider,
	Element: Element,
	ForwardRef: ForwardRef,
	Fragment: Fragment,
	Lazy: Lazy,
	Memo: Memo,
	Portal: Portal,
	Profiler: Profiler,
	StrictMode: StrictMode,
	Suspense: Suspense,
	isAsyncMode: isAsyncMode,
	isConcurrentMode: isConcurrentMode,
	isContextConsumer: isContextConsumer,
	isContextProvider: isContextProvider,
	isElement: isElement,
	isForwardRef: isForwardRef,
	isFragment: isFragment,
	isLazy: isLazy,
	isMemo: isMemo,
	isPortal: isPortal,
	isProfiler: isProfiler,
	isStrictMode: isStrictMode,
	isSuspense: isSuspense,
	isValidElementType: isValidElementType,
	typeOf: typeOf
};

var reactIs_development = createCommonjsModule(function (module, exports) {



if (process.env.NODE_ENV !== "production") {
  (function() {

// The Symbol used to tag the ReactElement-like types. If there is no native Symbol
// nor polyfill, then a plain number is used for performance.
var hasSymbol = typeof Symbol === 'function' && Symbol.for;
var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
// (unstable) APIs that have been removed. Can we remove the symbols?

var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;

function isValidElementType(type) {
  return typeof type === 'string' || typeof type === 'function' || // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
  type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
}

function typeOf(object) {
  if (typeof object === 'object' && object !== null) {
    var $$typeof = object.$$typeof;

    switch ($$typeof) {
      case REACT_ELEMENT_TYPE:
        var type = object.type;

        switch (type) {
          case REACT_ASYNC_MODE_TYPE:
          case REACT_CONCURRENT_MODE_TYPE:
          case REACT_FRAGMENT_TYPE:
          case REACT_PROFILER_TYPE:
          case REACT_STRICT_MODE_TYPE:
          case REACT_SUSPENSE_TYPE:
            return type;

          default:
            var $$typeofType = type && type.$$typeof;

            switch ($$typeofType) {
              case REACT_CONTEXT_TYPE:
              case REACT_FORWARD_REF_TYPE:
              case REACT_LAZY_TYPE:
              case REACT_MEMO_TYPE:
              case REACT_PROVIDER_TYPE:
                return $$typeofType;

              default:
                return $$typeof;
            }

        }

      case REACT_PORTAL_TYPE:
        return $$typeof;
    }
  }

  return undefined;
} // AsyncMode is deprecated along with isAsyncMode

var AsyncMode = REACT_ASYNC_MODE_TYPE;
var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
var ContextConsumer = REACT_CONTEXT_TYPE;
var ContextProvider = REACT_PROVIDER_TYPE;
var Element = REACT_ELEMENT_TYPE;
var ForwardRef = REACT_FORWARD_REF_TYPE;
var Fragment = REACT_FRAGMENT_TYPE;
var Lazy = REACT_LAZY_TYPE;
var Memo = REACT_MEMO_TYPE;
var Portal = REACT_PORTAL_TYPE;
var Profiler = REACT_PROFILER_TYPE;
var StrictMode = REACT_STRICT_MODE_TYPE;
var Suspense = REACT_SUSPENSE_TYPE;
var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

function isAsyncMode(object) {
  {
    if (!hasWarnedAboutDeprecatedIsAsyncMode) {
      hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

      console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
    }
  }

  return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
}
function isConcurrentMode(object) {
  return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
}
function isContextConsumer(object) {
  return typeOf(object) === REACT_CONTEXT_TYPE;
}
function isContextProvider(object) {
  return typeOf(object) === REACT_PROVIDER_TYPE;
}
function isElement(object) {
  return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
}
function isForwardRef(object) {
  return typeOf(object) === REACT_FORWARD_REF_TYPE;
}
function isFragment(object) {
  return typeOf(object) === REACT_FRAGMENT_TYPE;
}
function isLazy(object) {
  return typeOf(object) === REACT_LAZY_TYPE;
}
function isMemo(object) {
  return typeOf(object) === REACT_MEMO_TYPE;
}
function isPortal(object) {
  return typeOf(object) === REACT_PORTAL_TYPE;
}
function isProfiler(object) {
  return typeOf(object) === REACT_PROFILER_TYPE;
}
function isStrictMode(object) {
  return typeOf(object) === REACT_STRICT_MODE_TYPE;
}
function isSuspense(object) {
  return typeOf(object) === REACT_SUSPENSE_TYPE;
}

exports.AsyncMode = AsyncMode;
exports.ConcurrentMode = ConcurrentMode;
exports.ContextConsumer = ContextConsumer;
exports.ContextProvider = ContextProvider;
exports.Element = Element;
exports.ForwardRef = ForwardRef;
exports.Fragment = Fragment;
exports.Lazy = Lazy;
exports.Memo = Memo;
exports.Portal = Portal;
exports.Profiler = Profiler;
exports.StrictMode = StrictMode;
exports.Suspense = Suspense;
exports.isAsyncMode = isAsyncMode;
exports.isConcurrentMode = isConcurrentMode;
exports.isContextConsumer = isContextConsumer;
exports.isContextProvider = isContextProvider;
exports.isElement = isElement;
exports.isForwardRef = isForwardRef;
exports.isFragment = isFragment;
exports.isLazy = isLazy;
exports.isMemo = isMemo;
exports.isPortal = isPortal;
exports.isProfiler = isProfiler;
exports.isStrictMode = isStrictMode;
exports.isSuspense = isSuspense;
exports.isValidElementType = isValidElementType;
exports.typeOf = typeOf;
  })();
}
});
reactIs_development.AsyncMode;
reactIs_development.ConcurrentMode;
reactIs_development.ContextConsumer;
reactIs_development.ContextProvider;
reactIs_development.Element;
reactIs_development.ForwardRef;
reactIs_development.Fragment;
reactIs_development.Lazy;
reactIs_development.Memo;
reactIs_development.Portal;
reactIs_development.Profiler;
reactIs_development.StrictMode;
reactIs_development.Suspense;
reactIs_development.isAsyncMode;
reactIs_development.isConcurrentMode;
reactIs_development.isContextConsumer;
reactIs_development.isContextProvider;
reactIs_development.isElement;
reactIs_development.isForwardRef;
reactIs_development.isFragment;
reactIs_development.isLazy;
reactIs_development.isMemo;
reactIs_development.isPortal;
reactIs_development.isProfiler;
reactIs_development.isStrictMode;
reactIs_development.isSuspense;
reactIs_development.isValidElementType;
reactIs_development.typeOf;

var reactIs = createCommonjsModule(function (module) {

if (process.env.NODE_ENV === 'production') {
  module.exports = reactIs_production_min;
} else {
  module.exports = reactIs_development;
}
});

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/
/* eslint-disable no-unused-vars */
var getOwnPropertySymbols = Object.getOwnPropertySymbols;
var hasOwnProperty = Object.prototype.hasOwnProperty;
var propIsEnumerable = Object.prototype.propertyIsEnumerable;

function toObject(val) {
	if (val === null || val === undefined) {
		throw new TypeError('Object.assign cannot be called with null or undefined');
	}

	return Object(val);
}

function shouldUseNative() {
	try {
		if (!Object.assign) {
			return false;
		}

		// Detect buggy property enumeration order in older V8 versions.

		// https://bugs.chromium.org/p/v8/issues/detail?id=4118
		var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
		test1[5] = 'de';
		if (Object.getOwnPropertyNames(test1)[0] === '5') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test2 = {};
		for (var i = 0; i < 10; i++) {
			test2['_' + String.fromCharCode(i)] = i;
		}
		var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
			return test2[n];
		});
		if (order2.join('') !== '0123456789') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test3 = {};
		'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
			test3[letter] = letter;
		});
		if (Object.keys(Object.assign({}, test3)).join('') !==
				'abcdefghijklmnopqrst') {
			return false;
		}

		return true;
	} catch (err) {
		// We don't expect any of the above to throw, but better to be safe.
		return false;
	}
}

var objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
	var from;
	var to = toObject(target);
	var symbols;

	for (var s = 1; s < arguments.length; s++) {
		from = Object(arguments[s]);

		for (var key in from) {
			if (hasOwnProperty.call(from, key)) {
				to[key] = from[key];
			}
		}

		if (getOwnPropertySymbols) {
			symbols = getOwnPropertySymbols(from);
			for (var i = 0; i < symbols.length; i++) {
				if (propIsEnumerable.call(from, symbols[i])) {
					to[symbols[i]] = from[symbols[i]];
				}
			}
		}
	}

	return to;
};

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var ReactPropTypesSecret$2 = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

var ReactPropTypesSecret_1 = ReactPropTypesSecret$2;

var has$2 = Function.call.bind(Object.prototype.hasOwnProperty);

var ReactPropTypesSecret$1 = ReactPropTypesSecret_1;

var has$1 = has$2;

var printWarning$1 = function() {};

if (process.env.NODE_ENV !== 'production') {
  var ReactPropTypesSecret = ReactPropTypesSecret$1;
  var loggedTypeFailures = {};
  var has = has$1;

  printWarning$1 = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) { /**/ }
  };
}

/**
 * Assert that the values match with the type specs.
 * Error messages are memorized and will only be shown once.
 *
 * @param {object} typeSpecs Map of name to a ReactPropType
 * @param {object} values Runtime values that need to be type-checked
 * @param {string} location e.g. "prop", "context", "child context"
 * @param {string} componentName Name of the component for error messages.
 * @param {?Function} getStack Returns the component stack.
 * @private
 */
function checkPropTypes$1(typeSpecs, values, location, componentName, getStack) {
  if (process.env.NODE_ENV !== 'production') {
    for (var typeSpecName in typeSpecs) {
      if (has(typeSpecs, typeSpecName)) {
        var error;
        // Prop type validation may throw. In case they do, we don't want to
        // fail the render phase where it didn't fail before. So we log it.
        // After these have been cleaned up, we'll let them throw.
        try {
          // This is intentionally an invariant that gets caught. It's the same
          // behavior as without this statement except with a better message.
          if (typeof typeSpecs[typeSpecName] !== 'function') {
            var err = Error(
              (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
              'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.' +
              'This often happens because of typos such as `PropTypes.function` instead of `PropTypes.func`.'
            );
            err.name = 'Invariant Violation';
            throw err;
          }
          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret);
        } catch (ex) {
          error = ex;
        }
        if (error && !(error instanceof Error)) {
          printWarning$1(
            (componentName || 'React class') + ': type specification of ' +
            location + ' `' + typeSpecName + '` is invalid; the type checker ' +
            'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
            'You may have forgotten to pass an argument to the type checker ' +
            'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
            'shape all require an argument).'
          );
        }
        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
          // Only monitor this failure once because there tends to be a lot of the
          // same error.
          loggedTypeFailures[error.message] = true;

          var stack = getStack ? getStack() : '';

          printWarning$1(
            'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
          );
        }
      }
    }
  }
}

/**
 * Resets warning cache when testing.
 *
 * @private
 */
checkPropTypes$1.resetWarningCache = function() {
  if (process.env.NODE_ENV !== 'production') {
    loggedTypeFailures = {};
  }
};

var checkPropTypes_1 = checkPropTypes$1;

var checkPropTypes = checkPropTypes_1;

var printWarning = function() {};

if (process.env.NODE_ENV !== 'production') {
  printWarning = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

function emptyFunctionThatReturnsNull() {
  return null;
}

var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
  /* global Symbol */
  var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
  var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

  /**
   * Returns the iterator method function contained on the iterable object.
   *
   * Be sure to invoke the function with the iterable as context:
   *
   *     var iteratorFn = getIteratorFn(myIterable);
   *     if (iteratorFn) {
   *       var iterator = iteratorFn.call(myIterable);
   *       ...
   *     }
   *
   * @param {?object} maybeIterable
   * @return {?function}
   */
  function getIteratorFn(maybeIterable) {
    var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
    if (typeof iteratorFn === 'function') {
      return iteratorFn;
    }
  }

  /**
   * Collection of methods that allow declaration and validation of props that are
   * supplied to React components. Example usage:
   *
   *   var Props = require('ReactPropTypes');
   *   var MyArticle = React.createClass({
   *     propTypes: {
   *       // An optional string prop named "description".
   *       description: Props.string,
   *
   *       // A required enum prop named "category".
   *       category: Props.oneOf(['News','Photos']).isRequired,
   *
   *       // A prop named "dialog" that requires an instance of Dialog.
   *       dialog: Props.instanceOf(Dialog).isRequired
   *     },
   *     render: function() { ... }
   *   });
   *
   * A more formal specification of how these methods are used:
   *
   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
   *   decl := ReactPropTypes.{type}(.isRequired)?
   *
   * Each and every declaration produces a function with the same signature. This
   * allows the creation of custom validation functions. For example:
   *
   *  var MyLink = React.createClass({
   *    propTypes: {
   *      // An optional string or URI prop named "href".
   *      href: function(props, propName, componentName) {
   *        var propValue = props[propName];
   *        if (propValue != null && typeof propValue !== 'string' &&
   *            !(propValue instanceof URI)) {
   *          return new Error(
   *            'Expected a string or an URI for ' + propName + ' in ' +
   *            componentName
   *          );
   *        }
   *      }
   *    },
   *    render: function() {...}
   *  });
   *
   * @internal
   */

  var ANONYMOUS = '<<anonymous>>';

  // Important!
  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
  var ReactPropTypes = {
    array: createPrimitiveTypeChecker('array'),
    bigint: createPrimitiveTypeChecker('bigint'),
    bool: createPrimitiveTypeChecker('boolean'),
    func: createPrimitiveTypeChecker('function'),
    number: createPrimitiveTypeChecker('number'),
    object: createPrimitiveTypeChecker('object'),
    string: createPrimitiveTypeChecker('string'),
    symbol: createPrimitiveTypeChecker('symbol'),

    any: createAnyTypeChecker(),
    arrayOf: createArrayOfTypeChecker,
    element: createElementTypeChecker(),
    elementType: createElementTypeTypeChecker(),
    instanceOf: createInstanceTypeChecker,
    node: createNodeChecker(),
    objectOf: createObjectOfTypeChecker,
    oneOf: createEnumTypeChecker,
    oneOfType: createUnionTypeChecker,
    shape: createShapeTypeChecker,
    exact: createStrictShapeTypeChecker,
  };

  /**
   * inlined Object.is polyfill to avoid requiring consumers ship their own
   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
   */
  /*eslint-disable no-self-compare*/
  function is(x, y) {
    // SameValue algorithm
    if (x === y) {
      // Steps 1-5, 7-10
      // Steps 6.b-6.e: +0 != -0
      return x !== 0 || 1 / x === 1 / y;
    } else {
      // Step 6.a: NaN == NaN
      return x !== x && y !== y;
    }
  }
  /*eslint-enable no-self-compare*/

  /**
   * We use an Error-like object for backward compatibility as people may call
   * PropTypes directly and inspect their output. However, we don't use real
   * Errors anymore. We don't inspect their stack anyway, and creating them
   * is prohibitively expensive if they are created too often, such as what
   * happens in oneOfType() for any type before the one that matched.
   */
  function PropTypeError(message, data) {
    this.message = message;
    this.data = data && typeof data === 'object' ? data: {};
    this.stack = '';
  }
  // Make `instanceof Error` still work for returned errors.
  PropTypeError.prototype = Error.prototype;

  function createChainableTypeChecker(validate) {
    if (process.env.NODE_ENV !== 'production') {
      var manualPropTypeCallCache = {};
      var manualPropTypeWarningCount = 0;
    }
    function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
      componentName = componentName || ANONYMOUS;
      propFullName = propFullName || propName;

      if (secret !== ReactPropTypesSecret$1) {
        if (throwOnDirectAccess) {
          // New behavior only for users of `prop-types` package
          var err = new Error(
            'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
            'Use `PropTypes.checkPropTypes()` to call them. ' +
            'Read more at http://fb.me/use-check-prop-types'
          );
          err.name = 'Invariant Violation';
          throw err;
        } else if (process.env.NODE_ENV !== 'production' && typeof console !== 'undefined') {
          // Old behavior for people using React.PropTypes
          var cacheKey = componentName + ':' + propName;
          if (
            !manualPropTypeCallCache[cacheKey] &&
            // Avoid spamming the console because they are often not actionable except for lib authors
            manualPropTypeWarningCount < 3
          ) {
            printWarning(
              'You are manually calling a React.PropTypes validation ' +
              'function for the `' + propFullName + '` prop on `' + componentName + '`. This is deprecated ' +
              'and will throw in the standalone `prop-types` package. ' +
              'You may be seeing this warning due to a third-party PropTypes ' +
              'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
            );
            manualPropTypeCallCache[cacheKey] = true;
            manualPropTypeWarningCount++;
          }
        }
      }
      if (props[propName] == null) {
        if (isRequired) {
          if (props[propName] === null) {
            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
          }
          return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
        }
        return null;
      } else {
        return validate(props, propName, componentName, location, propFullName);
      }
    }

    var chainedCheckType = checkType.bind(null, false);
    chainedCheckType.isRequired = checkType.bind(null, true);

    return chainedCheckType;
  }

  function createPrimitiveTypeChecker(expectedType) {
    function validate(props, propName, componentName, location, propFullName, secret) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== expectedType) {
        // `propValue` being instance of, say, date/regexp, pass the 'object'
        // check, but we can offer a more precise error message here rather than
        // 'of type `object`'.
        var preciseType = getPreciseType(propValue);

        return new PropTypeError(
          'Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'),
          {expectedType: expectedType}
        );
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createAnyTypeChecker() {
    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
  }

  function createArrayOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
      }
      var propValue = props[propName];
      if (!Array.isArray(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
      }
      for (var i = 0; i < propValue.length; i++) {
        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret$1);
        if (error instanceof Error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!isValidElement(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!reactIs.isValidElementType(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createInstanceTypeChecker(expectedClass) {
    function validate(props, propName, componentName, location, propFullName) {
      if (!(props[propName] instanceof expectedClass)) {
        var expectedClassName = expectedClass.name || ANONYMOUS;
        var actualClassName = getClassName(props[propName]);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createEnumTypeChecker(expectedValues) {
    if (!Array.isArray(expectedValues)) {
      if (process.env.NODE_ENV !== 'production') {
        if (arguments.length > 1) {
          printWarning(
            'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
            'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
          );
        } else {
          printWarning('Invalid argument supplied to oneOf, expected an array.');
        }
      }
      return emptyFunctionThatReturnsNull;
    }

    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      for (var i = 0; i < expectedValues.length; i++) {
        if (is(propValue, expectedValues[i])) {
          return null;
        }
      }

      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
        var type = getPreciseType(value);
        if (type === 'symbol') {
          return String(value);
        }
        return value;
      });
      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createObjectOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
      }
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
      }
      for (var key in propValue) {
        if (has$1(propValue, key)) {
          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret$1);
          if (error instanceof Error) {
            return error;
          }
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createUnionTypeChecker(arrayOfTypeCheckers) {
    if (!Array.isArray(arrayOfTypeCheckers)) {
      process.env.NODE_ENV !== 'production' ? printWarning('Invalid argument supplied to oneOfType, expected an instance of array.') : void 0;
      return emptyFunctionThatReturnsNull;
    }

    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
      var checker = arrayOfTypeCheckers[i];
      if (typeof checker !== 'function') {
        printWarning(
          'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
          'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
        );
        return emptyFunctionThatReturnsNull;
      }
    }

    function validate(props, propName, componentName, location, propFullName) {
      var expectedTypes = [];
      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
        var checker = arrayOfTypeCheckers[i];
        var checkerResult = checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret$1);
        if (checkerResult == null) {
          return null;
        }
        if (checkerResult.data && has$1(checkerResult.data, 'expectedType')) {
          expectedTypes.push(checkerResult.data.expectedType);
        }
      }
      var expectedTypesMessage = (expectedTypes.length > 0) ? ', expected one of type [' + expectedTypes.join(', ') + ']': '';
      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`' + expectedTypesMessage + '.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createNodeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      if (!isNode(props[propName])) {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function invalidValidatorError(componentName, location, propFullName, key, type) {
    return new PropTypeError(
      (componentName || 'React class') + ': ' + location + ' type `' + propFullName + '.' + key + '` is invalid; ' +
      'it must be a function, usually from the `prop-types` package, but received `' + type + '`.'
    );
  }

  function createShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      for (var key in shapeTypes) {
        var checker = shapeTypes[key];
        if (typeof checker !== 'function') {
          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret$1);
        if (error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createStrictShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      // We need to check all keys in case some are required but missing from props.
      var allKeys = objectAssign({}, props[propName], shapeTypes);
      for (var key in allKeys) {
        var checker = shapeTypes[key];
        if (has$1(shapeTypes, key) && typeof checker !== 'function') {
          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
        }
        if (!checker) {
          return new PropTypeError(
            'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
            '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
            '\nValid keys: ' + JSON.stringify(Object.keys(shapeTypes), null, '  ')
          );
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret$1);
        if (error) {
          return error;
        }
      }
      return null;
    }

    return createChainableTypeChecker(validate);
  }

  function isNode(propValue) {
    switch (typeof propValue) {
      case 'number':
      case 'string':
      case 'undefined':
        return true;
      case 'boolean':
        return !propValue;
      case 'object':
        if (Array.isArray(propValue)) {
          return propValue.every(isNode);
        }
        if (propValue === null || isValidElement(propValue)) {
          return true;
        }

        var iteratorFn = getIteratorFn(propValue);
        if (iteratorFn) {
          var iterator = iteratorFn.call(propValue);
          var step;
          if (iteratorFn !== propValue.entries) {
            while (!(step = iterator.next()).done) {
              if (!isNode(step.value)) {
                return false;
              }
            }
          } else {
            // Iterator will provide entry [k,v] tuples rather than values.
            while (!(step = iterator.next()).done) {
              var entry = step.value;
              if (entry) {
                if (!isNode(entry[1])) {
                  return false;
                }
              }
            }
          }
        } else {
          return false;
        }

        return true;
      default:
        return false;
    }
  }

  function isSymbol(propType, propValue) {
    // Native Symbol.
    if (propType === 'symbol') {
      return true;
    }

    // falsy value can't be a Symbol
    if (!propValue) {
      return false;
    }

    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
    if (propValue['@@toStringTag'] === 'Symbol') {
      return true;
    }

    // Fallback for non-spec compliant Symbols which are polyfilled.
    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
      return true;
    }

    return false;
  }

  // Equivalent of `typeof` but with special handling for array and regexp.
  function getPropType(propValue) {
    var propType = typeof propValue;
    if (Array.isArray(propValue)) {
      return 'array';
    }
    if (propValue instanceof RegExp) {
      // Old webkits (at least until Android 4.0) return 'function' rather than
      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
      // passes PropTypes.object.
      return 'object';
    }
    if (isSymbol(propType, propValue)) {
      return 'symbol';
    }
    return propType;
  }

  // This handles more types than `getPropType`. Only used for error messages.
  // See `createPrimitiveTypeChecker`.
  function getPreciseType(propValue) {
    if (typeof propValue === 'undefined' || propValue === null) {
      return '' + propValue;
    }
    var propType = getPropType(propValue);
    if (propType === 'object') {
      if (propValue instanceof Date) {
        return 'date';
      } else if (propValue instanceof RegExp) {
        return 'regexp';
      }
    }
    return propType;
  }

  // Returns a string that is postfixed to a warning about an invalid type.
  // For example, "undefined" or "of type array"
  function getPostfixForTypeWarning(value) {
    var type = getPreciseType(value);
    switch (type) {
      case 'array':
      case 'object':
        return 'an ' + type;
      case 'boolean':
      case 'date':
      case 'regexp':
        return 'a ' + type;
      default:
        return type;
    }
  }

  // Returns class name of the object, if any.
  function getClassName(propValue) {
    if (!propValue.constructor || !propValue.constructor.name) {
      return ANONYMOUS;
    }
    return propValue.constructor.name;
  }

  ReactPropTypes.checkPropTypes = checkPropTypes;
  ReactPropTypes.resetWarningCache = checkPropTypes.resetWarningCache;
  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

function emptyFunction() {}
function emptyFunctionWithReset() {}
emptyFunctionWithReset.resetWarningCache = emptyFunction;

var factoryWithThrowingShims = function() {
  function shim(props, propName, componentName, location, propFullName, secret) {
    if (secret === ReactPropTypesSecret$1) {
      // It is still safe when called from React.
      return;
    }
    var err = new Error(
      'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
      'Use PropTypes.checkPropTypes() to call them. ' +
      'Read more at http://fb.me/use-check-prop-types'
    );
    err.name = 'Invariant Violation';
    throw err;
  }  shim.isRequired = shim;
  function getShim() {
    return shim;
  }  // Important!
  // Keep this list in sync with production version in `./factoryWithTypeCheckers.js`.
  var ReactPropTypes = {
    array: shim,
    bigint: shim,
    bool: shim,
    func: shim,
    number: shim,
    object: shim,
    string: shim,
    symbol: shim,

    any: shim,
    arrayOf: getShim,
    element: shim,
    elementType: shim,
    instanceOf: getShim,
    node: shim,
    objectOf: getShim,
    oneOf: getShim,
    oneOfType: getShim,
    shape: getShim,
    exact: getShim,

    checkPropTypes: emptyFunctionWithReset,
    resetWarningCache: emptyFunction
  };

  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

var require$$1 = factoryWithTypeCheckers;

var require$$2 = factoryWithThrowingShims;

var propTypes = createCommonjsModule(function (module) {
/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

if (process.env.NODE_ENV !== 'production') {
  var ReactIs = reactIs;

  // By explicitly using `prop-types` you are opting into new development behavior.
  // http://fb.me/prop-types-in-prod
  var throwOnDirectAccess = true;
  module.exports = require$$1(ReactIs.isElement, throwOnDirectAccess);
} else {
  // By explicitly using `prop-types` you are opting into new production behavior.
  // http://fb.me/prop-types-in-prod
  module.exports = require$$2();
}
});

var PropTypes = propTypes;

var immutable = createCommonjsModule(function (module, exports) {
/**
 *  Copyright (c) 2014-2015, Facebook, Inc.
 *  All rights reserved.
 *
 *  This source code is licensed under the BSD-style license found in the
 *  LICENSE file in the root directory of this source tree. An additional grant
 *  of patent rights can be found in the PATENTS file in the same directory.
 */

(function (global, factory) {
  module.exports = factory() ;
}(commonjsGlobal, function () {var SLICE$0 = Array.prototype.slice;

  function createClass(ctor, superClass) {
    if (superClass) {
      ctor.prototype = Object.create(superClass.prototype);
    }
    ctor.prototype.constructor = ctor;
  }

  function Iterable(value) {
      return isIterable(value) ? value : Seq(value);
    }


  createClass(KeyedIterable, Iterable);
    function KeyedIterable(value) {
      return isKeyed(value) ? value : KeyedSeq(value);
    }


  createClass(IndexedIterable, Iterable);
    function IndexedIterable(value) {
      return isIndexed(value) ? value : IndexedSeq(value);
    }


  createClass(SetIterable, Iterable);
    function SetIterable(value) {
      return isIterable(value) && !isAssociative(value) ? value : SetSeq(value);
    }



  function isIterable(maybeIterable) {
    return !!(maybeIterable && maybeIterable[IS_ITERABLE_SENTINEL]);
  }

  function isKeyed(maybeKeyed) {
    return !!(maybeKeyed && maybeKeyed[IS_KEYED_SENTINEL]);
  }

  function isIndexed(maybeIndexed) {
    return !!(maybeIndexed && maybeIndexed[IS_INDEXED_SENTINEL]);
  }

  function isAssociative(maybeAssociative) {
    return isKeyed(maybeAssociative) || isIndexed(maybeAssociative);
  }

  function isOrdered(maybeOrdered) {
    return !!(maybeOrdered && maybeOrdered[IS_ORDERED_SENTINEL]);
  }

  Iterable.isIterable = isIterable;
  Iterable.isKeyed = isKeyed;
  Iterable.isIndexed = isIndexed;
  Iterable.isAssociative = isAssociative;
  Iterable.isOrdered = isOrdered;

  Iterable.Keyed = KeyedIterable;
  Iterable.Indexed = IndexedIterable;
  Iterable.Set = SetIterable;


  var IS_ITERABLE_SENTINEL = '@@__IMMUTABLE_ITERABLE__@@';
  var IS_KEYED_SENTINEL = '@@__IMMUTABLE_KEYED__@@';
  var IS_INDEXED_SENTINEL = '@@__IMMUTABLE_INDEXED__@@';
  var IS_ORDERED_SENTINEL = '@@__IMMUTABLE_ORDERED__@@';

  // Used for setting prototype methods that IE8 chokes on.
  var DELETE = 'delete';

  // Constants describing the size of trie nodes.
  var SHIFT = 5; // Resulted in best performance after ______?
  var SIZE = 1 << SHIFT;
  var MASK = SIZE - 1;

  // A consistent shared value representing "not set" which equals nothing other
  // than itself, and nothing that could be provided externally.
  var NOT_SET = {};

  // Boolean references, Rough equivalent of `bool &`.
  var CHANGE_LENGTH = { value: false };
  var DID_ALTER = { value: false };

  function MakeRef(ref) {
    ref.value = false;
    return ref;
  }

  function SetRef(ref) {
    ref && (ref.value = true);
  }

  // A function which returns a value representing an "owner" for transient writes
  // to tries. The return value will only ever equal itself, and will not equal
  // the return of any subsequent call of this function.
  function OwnerID() {}

  // http://jsperf.com/copy-array-inline
  function arrCopy(arr, offset) {
    offset = offset || 0;
    var len = Math.max(0, arr.length - offset);
    var newArr = new Array(len);
    for (var ii = 0; ii < len; ii++) {
      newArr[ii] = arr[ii + offset];
    }
    return newArr;
  }

  function ensureSize(iter) {
    if (iter.size === undefined) {
      iter.size = iter.__iterate(returnTrue);
    }
    return iter.size;
  }

  function wrapIndex(iter, index) {
    // This implements "is array index" which the ECMAString spec defines as:
    //
    //     A String property name P is an array index if and only if
    //     ToString(ToUint32(P)) is equal to P and ToUint32(P) is not equal
    //     to 2^32−1.
    //
    // http://www.ecma-international.org/ecma-262/6.0/#sec-array-exotic-objects
    if (typeof index !== 'number') {
      var uint32Index = index >>> 0; // N >>> 0 is shorthand for ToUint32
      if ('' + uint32Index !== index || uint32Index === 4294967295) {
        return NaN;
      }
      index = uint32Index;
    }
    return index < 0 ? ensureSize(iter) + index : index;
  }

  function returnTrue() {
    return true;
  }

  function wholeSlice(begin, end, size) {
    return (begin === 0 || (size !== undefined && begin <= -size)) &&
      (end === undefined || (size !== undefined && end >= size));
  }

  function resolveBegin(begin, size) {
    return resolveIndex(begin, size, 0);
  }

  function resolveEnd(end, size) {
    return resolveIndex(end, size, size);
  }

  function resolveIndex(index, size, defaultIndex) {
    return index === undefined ?
      defaultIndex :
      index < 0 ?
        Math.max(0, size + index) :
        size === undefined ?
          index :
          Math.min(size, index);
  }

  /* global Symbol */

  var ITERATE_KEYS = 0;
  var ITERATE_VALUES = 1;
  var ITERATE_ENTRIES = 2;

  var REAL_ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
  var FAUX_ITERATOR_SYMBOL = '@@iterator';

  var ITERATOR_SYMBOL = REAL_ITERATOR_SYMBOL || FAUX_ITERATOR_SYMBOL;


  function Iterator(next) {
      this.next = next;
    }

    Iterator.prototype.toString = function() {
      return '[Iterator]';
    };


  Iterator.KEYS = ITERATE_KEYS;
  Iterator.VALUES = ITERATE_VALUES;
  Iterator.ENTRIES = ITERATE_ENTRIES;

  Iterator.prototype.inspect =
  Iterator.prototype.toSource = function () { return this.toString(); };
  Iterator.prototype[ITERATOR_SYMBOL] = function () {
    return this;
  };


  function iteratorValue(type, k, v, iteratorResult) {
    var value = type === 0 ? k : type === 1 ? v : [k, v];
    iteratorResult ? (iteratorResult.value = value) : (iteratorResult = {
      value: value, done: false
    });
    return iteratorResult;
  }

  function iteratorDone() {
    return { value: undefined, done: true };
  }

  function hasIterator(maybeIterable) {
    return !!getIteratorFn(maybeIterable);
  }

  function isIterator(maybeIterator) {
    return maybeIterator && typeof maybeIterator.next === 'function';
  }

  function getIterator(iterable) {
    var iteratorFn = getIteratorFn(iterable);
    return iteratorFn && iteratorFn.call(iterable);
  }

  function getIteratorFn(iterable) {
    var iteratorFn = iterable && (
      (REAL_ITERATOR_SYMBOL && iterable[REAL_ITERATOR_SYMBOL]) ||
      iterable[FAUX_ITERATOR_SYMBOL]
    );
    if (typeof iteratorFn === 'function') {
      return iteratorFn;
    }
  }

  function isArrayLike(value) {
    return value && typeof value.length === 'number';
  }

  createClass(Seq, Iterable);
    function Seq(value) {
      return value === null || value === undefined ? emptySequence() :
        isIterable(value) ? value.toSeq() : seqFromValue(value);
    }

    Seq.of = function(/*...values*/) {
      return Seq(arguments);
    };

    Seq.prototype.toSeq = function() {
      return this;
    };

    Seq.prototype.toString = function() {
      return this.__toString('Seq {', '}');
    };

    Seq.prototype.cacheResult = function() {
      if (!this._cache && this.__iterateUncached) {
        this._cache = this.entrySeq().toArray();
        this.size = this._cache.length;
      }
      return this;
    };

    // abstract __iterateUncached(fn, reverse)

    Seq.prototype.__iterate = function(fn, reverse) {
      return seqIterate(this, fn, reverse, true);
    };

    // abstract __iteratorUncached(type, reverse)

    Seq.prototype.__iterator = function(type, reverse) {
      return seqIterator(this, type, reverse, true);
    };



  createClass(KeyedSeq, Seq);
    function KeyedSeq(value) {
      return value === null || value === undefined ?
        emptySequence().toKeyedSeq() :
        isIterable(value) ?
          (isKeyed(value) ? value.toSeq() : value.fromEntrySeq()) :
          keyedSeqFromValue(value);
    }

    KeyedSeq.prototype.toKeyedSeq = function() {
      return this;
    };



  createClass(IndexedSeq, Seq);
    function IndexedSeq(value) {
      return value === null || value === undefined ? emptySequence() :
        !isIterable(value) ? indexedSeqFromValue(value) :
        isKeyed(value) ? value.entrySeq() : value.toIndexedSeq();
    }

    IndexedSeq.of = function(/*...values*/) {
      return IndexedSeq(arguments);
    };

    IndexedSeq.prototype.toIndexedSeq = function() {
      return this;
    };

    IndexedSeq.prototype.toString = function() {
      return this.__toString('Seq [', ']');
    };

    IndexedSeq.prototype.__iterate = function(fn, reverse) {
      return seqIterate(this, fn, reverse, false);
    };

    IndexedSeq.prototype.__iterator = function(type, reverse) {
      return seqIterator(this, type, reverse, false);
    };



  createClass(SetSeq, Seq);
    function SetSeq(value) {
      return (
        value === null || value === undefined ? emptySequence() :
        !isIterable(value) ? indexedSeqFromValue(value) :
        isKeyed(value) ? value.entrySeq() : value
      ).toSetSeq();
    }

    SetSeq.of = function(/*...values*/) {
      return SetSeq(arguments);
    };

    SetSeq.prototype.toSetSeq = function() {
      return this;
    };



  Seq.isSeq = isSeq;
  Seq.Keyed = KeyedSeq;
  Seq.Set = SetSeq;
  Seq.Indexed = IndexedSeq;

  var IS_SEQ_SENTINEL = '@@__IMMUTABLE_SEQ__@@';

  Seq.prototype[IS_SEQ_SENTINEL] = true;



  createClass(ArraySeq, IndexedSeq);
    function ArraySeq(array) {
      this._array = array;
      this.size = array.length;
    }

    ArraySeq.prototype.get = function(index, notSetValue) {
      return this.has(index) ? this._array[wrapIndex(this, index)] : notSetValue;
    };

    ArraySeq.prototype.__iterate = function(fn, reverse) {
      var array = this._array;
      var maxIndex = array.length - 1;
      for (var ii = 0; ii <= maxIndex; ii++) {
        if (fn(array[reverse ? maxIndex - ii : ii], ii, this) === false) {
          return ii + 1;
        }
      }
      return ii;
    };

    ArraySeq.prototype.__iterator = function(type, reverse) {
      var array = this._array;
      var maxIndex = array.length - 1;
      var ii = 0;
      return new Iterator(function() 
        {return ii > maxIndex ?
          iteratorDone() :
          iteratorValue(type, ii, array[reverse ? maxIndex - ii++ : ii++])}
      );
    };



  createClass(ObjectSeq, KeyedSeq);
    function ObjectSeq(object) {
      var keys = Object.keys(object);
      this._object = object;
      this._keys = keys;
      this.size = keys.length;
    }

    ObjectSeq.prototype.get = function(key, notSetValue) {
      if (notSetValue !== undefined && !this.has(key)) {
        return notSetValue;
      }
      return this._object[key];
    };

    ObjectSeq.prototype.has = function(key) {
      return this._object.hasOwnProperty(key);
    };

    ObjectSeq.prototype.__iterate = function(fn, reverse) {
      var object = this._object;
      var keys = this._keys;
      var maxIndex = keys.length - 1;
      for (var ii = 0; ii <= maxIndex; ii++) {
        var key = keys[reverse ? maxIndex - ii : ii];
        if (fn(object[key], key, this) === false) {
          return ii + 1;
        }
      }
      return ii;
    };

    ObjectSeq.prototype.__iterator = function(type, reverse) {
      var object = this._object;
      var keys = this._keys;
      var maxIndex = keys.length - 1;
      var ii = 0;
      return new Iterator(function()  {
        var key = keys[reverse ? maxIndex - ii : ii];
        return ii++ > maxIndex ?
          iteratorDone() :
          iteratorValue(type, key, object[key]);
      });
    };

  ObjectSeq.prototype[IS_ORDERED_SENTINEL] = true;


  createClass(IterableSeq, IndexedSeq);
    function IterableSeq(iterable) {
      this._iterable = iterable;
      this.size = iterable.length || iterable.size;
    }

    IterableSeq.prototype.__iterateUncached = function(fn, reverse) {
      if (reverse) {
        return this.cacheResult().__iterate(fn, reverse);
      }
      var iterable = this._iterable;
      var iterator = getIterator(iterable);
      var iterations = 0;
      if (isIterator(iterator)) {
        var step;
        while (!(step = iterator.next()).done) {
          if (fn(step.value, iterations++, this) === false) {
            break;
          }
        }
      }
      return iterations;
    };

    IterableSeq.prototype.__iteratorUncached = function(type, reverse) {
      if (reverse) {
        return this.cacheResult().__iterator(type, reverse);
      }
      var iterable = this._iterable;
      var iterator = getIterator(iterable);
      if (!isIterator(iterator)) {
        return new Iterator(iteratorDone);
      }
      var iterations = 0;
      return new Iterator(function()  {
        var step = iterator.next();
        return step.done ? step : iteratorValue(type, iterations++, step.value);
      });
    };



  createClass(IteratorSeq, IndexedSeq);
    function IteratorSeq(iterator) {
      this._iterator = iterator;
      this._iteratorCache = [];
    }

    IteratorSeq.prototype.__iterateUncached = function(fn, reverse) {
      if (reverse) {
        return this.cacheResult().__iterate(fn, reverse);
      }
      var iterator = this._iterator;
      var cache = this._iteratorCache;
      var iterations = 0;
      while (iterations < cache.length) {
        if (fn(cache[iterations], iterations++, this) === false) {
          return iterations;
        }
      }
      var step;
      while (!(step = iterator.next()).done) {
        var val = step.value;
        cache[iterations] = val;
        if (fn(val, iterations++, this) === false) {
          break;
        }
      }
      return iterations;
    };

    IteratorSeq.prototype.__iteratorUncached = function(type, reverse) {
      if (reverse) {
        return this.cacheResult().__iterator(type, reverse);
      }
      var iterator = this._iterator;
      var cache = this._iteratorCache;
      var iterations = 0;
      return new Iterator(function()  {
        if (iterations >= cache.length) {
          var step = iterator.next();
          if (step.done) {
            return step;
          }
          cache[iterations] = step.value;
        }
        return iteratorValue(type, iterations, cache[iterations++]);
      });
    };




  // # pragma Helper functions

  function isSeq(maybeSeq) {
    return !!(maybeSeq && maybeSeq[IS_SEQ_SENTINEL]);
  }

  var EMPTY_SEQ;

  function emptySequence() {
    return EMPTY_SEQ || (EMPTY_SEQ = new ArraySeq([]));
  }

  function keyedSeqFromValue(value) {
    var seq =
      Array.isArray(value) ? new ArraySeq(value).fromEntrySeq() :
      isIterator(value) ? new IteratorSeq(value).fromEntrySeq() :
      hasIterator(value) ? new IterableSeq(value).fromEntrySeq() :
      typeof value === 'object' ? new ObjectSeq(value) :
      undefined;
    if (!seq) {
      throw new TypeError(
        'Expected Array or iterable object of [k, v] entries, '+
        'or keyed object: ' + value
      );
    }
    return seq;
  }

  function indexedSeqFromValue(value) {
    var seq = maybeIndexedSeqFromValue(value);
    if (!seq) {
      throw new TypeError(
        'Expected Array or iterable object of values: ' + value
      );
    }
    return seq;
  }

  function seqFromValue(value) {
    var seq = maybeIndexedSeqFromValue(value) ||
      (typeof value === 'object' && new ObjectSeq(value));
    if (!seq) {
      throw new TypeError(
        'Expected Array or iterable object of values, or keyed object: ' + value
      );
    }
    return seq;
  }

  function maybeIndexedSeqFromValue(value) {
    return (
      isArrayLike(value) ? new ArraySeq(value) :
      isIterator(value) ? new IteratorSeq(value) :
      hasIterator(value) ? new IterableSeq(value) :
      undefined
    );
  }

  function seqIterate(seq, fn, reverse, useKeys) {
    var cache = seq._cache;
    if (cache) {
      var maxIndex = cache.length - 1;
      for (var ii = 0; ii <= maxIndex; ii++) {
        var entry = cache[reverse ? maxIndex - ii : ii];
        if (fn(entry[1], useKeys ? entry[0] : ii, seq) === false) {
          return ii + 1;
        }
      }
      return ii;
    }
    return seq.__iterateUncached(fn, reverse);
  }

  function seqIterator(seq, type, reverse, useKeys) {
    var cache = seq._cache;
    if (cache) {
      var maxIndex = cache.length - 1;
      var ii = 0;
      return new Iterator(function()  {
        var entry = cache[reverse ? maxIndex - ii : ii];
        return ii++ > maxIndex ?
          iteratorDone() :
          iteratorValue(type, useKeys ? entry[0] : ii - 1, entry[1]);
      });
    }
    return seq.__iteratorUncached(type, reverse);
  }

  function fromJS(json, converter) {
    return converter ?
      fromJSWith(converter, json, '', {'': json}) :
      fromJSDefault(json);
  }

  function fromJSWith(converter, json, key, parentJSON) {
    if (Array.isArray(json)) {
      return converter.call(parentJSON, key, IndexedSeq(json).map(function(v, k)  {return fromJSWith(converter, v, k, json)}));
    }
    if (isPlainObj(json)) {
      return converter.call(parentJSON, key, KeyedSeq(json).map(function(v, k)  {return fromJSWith(converter, v, k, json)}));
    }
    return json;
  }

  function fromJSDefault(json) {
    if (Array.isArray(json)) {
      return IndexedSeq(json).map(fromJSDefault).toList();
    }
    if (isPlainObj(json)) {
      return KeyedSeq(json).map(fromJSDefault).toMap();
    }
    return json;
  }

  function isPlainObj(value) {
    return value && (value.constructor === Object || value.constructor === undefined);
  }

  /**
   * An extension of the "same-value" algorithm as [described for use by ES6 Map
   * and Set](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Map#Key_equality)
   *
   * NaN is considered the same as NaN, however -0 and 0 are considered the same
   * value, which is different from the algorithm described by
   * [`Object.is`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is).
   *
   * This is extended further to allow Objects to describe the values they
   * represent, by way of `valueOf` or `equals` (and `hashCode`).
   *
   * Note: because of this extension, the key equality of Immutable.Map and the
   * value equality of Immutable.Set will differ from ES6 Map and Set.
   *
   * ### Defining custom values
   *
   * The easiest way to describe the value an object represents is by implementing
   * `valueOf`. For example, `Date` represents a value by returning a unix
   * timestamp for `valueOf`:
   *
   *     var date1 = new Date(1234567890000); // Fri Feb 13 2009 ...
   *     var date2 = new Date(1234567890000);
   *     date1.valueOf(); // 1234567890000
   *     assert( date1 !== date2 );
   *     assert( Immutable.is( date1, date2 ) );
   *
   * Note: overriding `valueOf` may have other implications if you use this object
   * where JavaScript expects a primitive, such as implicit string coercion.
   *
   * For more complex types, especially collections, implementing `valueOf` may
   * not be performant. An alternative is to implement `equals` and `hashCode`.
   *
   * `equals` takes another object, presumably of similar type, and returns true
   * if the it is equal. Equality is symmetrical, so the same result should be
   * returned if this and the argument are flipped.
   *
   *     assert( a.equals(b) === b.equals(a) );
   *
   * `hashCode` returns a 32bit integer number representing the object which will
   * be used to determine how to store the value object in a Map or Set. You must
   * provide both or neither methods, one must not exist without the other.
   *
   * Also, an important relationship between these methods must be upheld: if two
   * values are equal, they *must* return the same hashCode. If the values are not
   * equal, they might have the same hashCode; this is called a hash collision,
   * and while undesirable for performance reasons, it is acceptable.
   *
   *     if (a.equals(b)) {
   *       assert( a.hashCode() === b.hashCode() );
   *     }
   *
   * All Immutable collections implement `equals` and `hashCode`.
   *
   */
  function is(valueA, valueB) {
    if (valueA === valueB || (valueA !== valueA && valueB !== valueB)) {
      return true;
    }
    if (!valueA || !valueB) {
      return false;
    }
    if (typeof valueA.valueOf === 'function' &&
        typeof valueB.valueOf === 'function') {
      valueA = valueA.valueOf();
      valueB = valueB.valueOf();
      if (valueA === valueB || (valueA !== valueA && valueB !== valueB)) {
        return true;
      }
      if (!valueA || !valueB) {
        return false;
      }
    }
    if (typeof valueA.equals === 'function' &&
        typeof valueB.equals === 'function' &&
        valueA.equals(valueB)) {
      return true;
    }
    return false;
  }

  function deepEqual(a, b) {
    if (a === b) {
      return true;
    }

    if (
      !isIterable(b) ||
      a.size !== undefined && b.size !== undefined && a.size !== b.size ||
      a.__hash !== undefined && b.__hash !== undefined && a.__hash !== b.__hash ||
      isKeyed(a) !== isKeyed(b) ||
      isIndexed(a) !== isIndexed(b) ||
      isOrdered(a) !== isOrdered(b)
    ) {
      return false;
    }

    if (a.size === 0 && b.size === 0) {
      return true;
    }

    var notAssociative = !isAssociative(a);

    if (isOrdered(a)) {
      var entries = a.entries();
      return b.every(function(v, k)  {
        var entry = entries.next().value;
        return entry && is(entry[1], v) && (notAssociative || is(entry[0], k));
      }) && entries.next().done;
    }

    var flipped = false;

    if (a.size === undefined) {
      if (b.size === undefined) {
        if (typeof a.cacheResult === 'function') {
          a.cacheResult();
        }
      } else {
        flipped = true;
        var _ = a;
        a = b;
        b = _;
      }
    }

    var allEqual = true;
    var bSize = b.__iterate(function(v, k)  {
      if (notAssociative ? !a.has(v) :
          flipped ? !is(v, a.get(k, NOT_SET)) : !is(a.get(k, NOT_SET), v)) {
        allEqual = false;
        return false;
      }
    });

    return allEqual && a.size === bSize;
  }

  createClass(Repeat, IndexedSeq);

    function Repeat(value, times) {
      if (!(this instanceof Repeat)) {
        return new Repeat(value, times);
      }
      this._value = value;
      this.size = times === undefined ? Infinity : Math.max(0, times);
      if (this.size === 0) {
        if (EMPTY_REPEAT) {
          return EMPTY_REPEAT;
        }
        EMPTY_REPEAT = this;
      }
    }

    Repeat.prototype.toString = function() {
      if (this.size === 0) {
        return 'Repeat []';
      }
      return 'Repeat [ ' + this._value + ' ' + this.size + ' times ]';
    };

    Repeat.prototype.get = function(index, notSetValue) {
      return this.has(index) ? this._value : notSetValue;
    };

    Repeat.prototype.includes = function(searchValue) {
      return is(this._value, searchValue);
    };

    Repeat.prototype.slice = function(begin, end) {
      var size = this.size;
      return wholeSlice(begin, end, size) ? this :
        new Repeat(this._value, resolveEnd(end, size) - resolveBegin(begin, size));
    };

    Repeat.prototype.reverse = function() {
      return this;
    };

    Repeat.prototype.indexOf = function(searchValue) {
      if (is(this._value, searchValue)) {
        return 0;
      }
      return -1;
    };

    Repeat.prototype.lastIndexOf = function(searchValue) {
      if (is(this._value, searchValue)) {
        return this.size;
      }
      return -1;
    };

    Repeat.prototype.__iterate = function(fn, reverse) {
      for (var ii = 0; ii < this.size; ii++) {
        if (fn(this._value, ii, this) === false) {
          return ii + 1;
        }
      }
      return ii;
    };

    Repeat.prototype.__iterator = function(type, reverse) {var this$0 = this;
      var ii = 0;
      return new Iterator(function() 
        {return ii < this$0.size ? iteratorValue(type, ii++, this$0._value) : iteratorDone()}
      );
    };

    Repeat.prototype.equals = function(other) {
      return other instanceof Repeat ?
        is(this._value, other._value) :
        deepEqual(other);
    };


  var EMPTY_REPEAT;

  function invariant(condition, error) {
    if (!condition) throw new Error(error);
  }

  createClass(Range, IndexedSeq);

    function Range(start, end, step) {
      if (!(this instanceof Range)) {
        return new Range(start, end, step);
      }
      invariant(step !== 0, 'Cannot step a Range by 0');
      start = start || 0;
      if (end === undefined) {
        end = Infinity;
      }
      step = step === undefined ? 1 : Math.abs(step);
      if (end < start) {
        step = -step;
      }
      this._start = start;
      this._end = end;
      this._step = step;
      this.size = Math.max(0, Math.ceil((end - start) / step - 1) + 1);
      if (this.size === 0) {
        if (EMPTY_RANGE) {
          return EMPTY_RANGE;
        }
        EMPTY_RANGE = this;
      }
    }

    Range.prototype.toString = function() {
      if (this.size === 0) {
        return 'Range []';
      }
      return 'Range [ ' +
        this._start + '...' + this._end +
        (this._step > 1 ? ' by ' + this._step : '') +
      ' ]';
    };

    Range.prototype.get = function(index, notSetValue) {
      return this.has(index) ?
        this._start + wrapIndex(this, index) * this._step :
        notSetValue;
    };

    Range.prototype.includes = function(searchValue) {
      var possibleIndex = (searchValue - this._start) / this._step;
      return possibleIndex >= 0 &&
        possibleIndex < this.size &&
        possibleIndex === Math.floor(possibleIndex);
    };

    Range.prototype.slice = function(begin, end) {
      if (wholeSlice(begin, end, this.size)) {
        return this;
      }
      begin = resolveBegin(begin, this.size);
      end = resolveEnd(end, this.size);
      if (end <= begin) {
        return new Range(0, 0);
      }
      return new Range(this.get(begin, this._end), this.get(end, this._end), this._step);
    };

    Range.prototype.indexOf = function(searchValue) {
      var offsetValue = searchValue - this._start;
      if (offsetValue % this._step === 0) {
        var index = offsetValue / this._step;
        if (index >= 0 && index < this.size) {
          return index
        }
      }
      return -1;
    };

    Range.prototype.lastIndexOf = function(searchValue) {
      return this.indexOf(searchValue);
    };

    Range.prototype.__iterate = function(fn, reverse) {
      var maxIndex = this.size - 1;
      var step = this._step;
      var value = reverse ? this._start + maxIndex * step : this._start;
      for (var ii = 0; ii <= maxIndex; ii++) {
        if (fn(value, ii, this) === false) {
          return ii + 1;
        }
        value += reverse ? -step : step;
      }
      return ii;
    };

    Range.prototype.__iterator = function(type, reverse) {
      var maxIndex = this.size - 1;
      var step = this._step;
      var value = reverse ? this._start + maxIndex * step : this._start;
      var ii = 0;
      return new Iterator(function()  {
        var v = value;
        value += reverse ? -step : step;
        return ii > maxIndex ? iteratorDone() : iteratorValue(type, ii++, v);
      });
    };

    Range.prototype.equals = function(other) {
      return other instanceof Range ?
        this._start === other._start &&
        this._end === other._end &&
        this._step === other._step :
        deepEqual(this, other);
    };


  var EMPTY_RANGE;

  createClass(Collection, Iterable);
    function Collection() {
      throw TypeError('Abstract');
    }


  createClass(KeyedCollection, Collection);function KeyedCollection() {}

  createClass(IndexedCollection, Collection);function IndexedCollection() {}

  createClass(SetCollection, Collection);function SetCollection() {}


  Collection.Keyed = KeyedCollection;
  Collection.Indexed = IndexedCollection;
  Collection.Set = SetCollection;

  var imul =
    typeof Math.imul === 'function' && Math.imul(0xffffffff, 2) === -2 ?
    Math.imul :
    function imul(a, b) {
      a = a | 0; // int
      b = b | 0; // int
      var c = a & 0xffff;
      var d = b & 0xffff;
      // Shift by 0 fixes the sign on the high part.
      return (c * d) + ((((a >>> 16) * d + c * (b >>> 16)) << 16) >>> 0) | 0; // int
    };

  // v8 has an optimization for storing 31-bit signed numbers.
  // Values which have either 00 or 11 as the high order bits qualify.
  // This function drops the highest order bit in a signed number, maintaining
  // the sign bit.
  function smi(i32) {
    return ((i32 >>> 1) & 0x40000000) | (i32 & 0xBFFFFFFF);
  }

  function hash(o) {
    if (o === false || o === null || o === undefined) {
      return 0;
    }
    if (typeof o.valueOf === 'function') {
      o = o.valueOf();
      if (o === false || o === null || o === undefined) {
        return 0;
      }
    }
    if (o === true) {
      return 1;
    }
    var type = typeof o;
    if (type === 'number') {
      var h = o | 0;
      if (h !== o) {
        h ^= o * 0xFFFFFFFF;
      }
      while (o > 0xFFFFFFFF) {
        o /= 0xFFFFFFFF;
        h ^= o;
      }
      return smi(h);
    }
    if (type === 'string') {
      return o.length > STRING_HASH_CACHE_MIN_STRLEN ? cachedHashString(o) : hashString(o);
    }
    if (typeof o.hashCode === 'function') {
      return o.hashCode();
    }
    if (type === 'object') {
      return hashJSObj(o);
    }
    if (typeof o.toString === 'function') {
      return hashString(o.toString());
    }
    throw new Error('Value type ' + type + ' cannot be hashed.');
  }

  function cachedHashString(string) {
    var hash = stringHashCache[string];
    if (hash === undefined) {
      hash = hashString(string);
      if (STRING_HASH_CACHE_SIZE === STRING_HASH_CACHE_MAX_SIZE) {
        STRING_HASH_CACHE_SIZE = 0;
        stringHashCache = {};
      }
      STRING_HASH_CACHE_SIZE++;
      stringHashCache[string] = hash;
    }
    return hash;
  }

  // http://jsperf.com/hashing-strings
  function hashString(string) {
    // This is the hash from JVM
    // The hash code for a string is computed as
    // s[0] * 31 ^ (n - 1) + s[1] * 31 ^ (n - 2) + ... + s[n - 1],
    // where s[i] is the ith character of the string and n is the length of
    // the string. We "mod" the result to make it between 0 (inclusive) and 2^31
    // (exclusive) by dropping high bits.
    var hash = 0;
    for (var ii = 0; ii < string.length; ii++) {
      hash = 31 * hash + string.charCodeAt(ii) | 0;
    }
    return smi(hash);
  }

  function hashJSObj(obj) {
    var hash;
    if (usingWeakMap) {
      hash = weakMap.get(obj);
      if (hash !== undefined) {
        return hash;
      }
    }

    hash = obj[UID_HASH_KEY];
    if (hash !== undefined) {
      return hash;
    }

    if (!canDefineProperty) {
      hash = obj.propertyIsEnumerable && obj.propertyIsEnumerable[UID_HASH_KEY];
      if (hash !== undefined) {
        return hash;
      }

      hash = getIENodeHash(obj);
      if (hash !== undefined) {
        return hash;
      }
    }

    hash = ++objHashUID;
    if (objHashUID & 0x40000000) {
      objHashUID = 0;
    }

    if (usingWeakMap) {
      weakMap.set(obj, hash);
    } else if (isExtensible !== undefined && isExtensible(obj) === false) {
      throw new Error('Non-extensible objects are not allowed as keys.');
    } else if (canDefineProperty) {
      Object.defineProperty(obj, UID_HASH_KEY, {
        'enumerable': false,
        'configurable': false,
        'writable': false,
        'value': hash
      });
    } else if (obj.propertyIsEnumerable !== undefined &&
               obj.propertyIsEnumerable === obj.constructor.prototype.propertyIsEnumerable) {
      // Since we can't define a non-enumerable property on the object
      // we'll hijack one of the less-used non-enumerable properties to
      // save our hash on it. Since this is a function it will not show up in
      // `JSON.stringify` which is what we want.
      obj.propertyIsEnumerable = function() {
        return this.constructor.prototype.propertyIsEnumerable.apply(this, arguments);
      };
      obj.propertyIsEnumerable[UID_HASH_KEY] = hash;
    } else if (obj.nodeType !== undefined) {
      // At this point we couldn't get the IE `uniqueID` to use as a hash
      // and we couldn't use a non-enumerable property to exploit the
      // dontEnum bug so we simply add the `UID_HASH_KEY` on the node
      // itself.
      obj[UID_HASH_KEY] = hash;
    } else {
      throw new Error('Unable to set a non-enumerable property on object.');
    }

    return hash;
  }

  // Get references to ES5 object methods.
  var isExtensible = Object.isExtensible;

  // True if Object.defineProperty works as expected. IE8 fails this test.
  var canDefineProperty = (function() {
    try {
      Object.defineProperty({}, '@', {});
      return true;
    } catch (e) {
      return false;
    }
  }());

  // IE has a `uniqueID` property on DOM nodes. We can construct the hash from it
  // and avoid memory leaks from the IE cloneNode bug.
  function getIENodeHash(node) {
    if (node && node.nodeType > 0) {
      switch (node.nodeType) {
        case 1: // Element
          return node.uniqueID;
        case 9: // Document
          return node.documentElement && node.documentElement.uniqueID;
      }
    }
  }

  // If possible, use a WeakMap.
  var usingWeakMap = typeof WeakMap === 'function';
  var weakMap;
  if (usingWeakMap) {
    weakMap = new WeakMap();
  }

  var objHashUID = 0;

  var UID_HASH_KEY = '__immutablehash__';
  if (typeof Symbol === 'function') {
    UID_HASH_KEY = Symbol(UID_HASH_KEY);
  }

  var STRING_HASH_CACHE_MIN_STRLEN = 16;
  var STRING_HASH_CACHE_MAX_SIZE = 255;
  var STRING_HASH_CACHE_SIZE = 0;
  var stringHashCache = {};

  function assertNotInfinite(size) {
    invariant(
      size !== Infinity,
      'Cannot perform this action with an infinite size.'
    );
  }

  createClass(Map, KeyedCollection);

    // @pragma Construction

    function Map(value) {
      return value === null || value === undefined ? emptyMap() :
        isMap(value) && !isOrdered(value) ? value :
        emptyMap().withMutations(function(map ) {
          var iter = KeyedIterable(value);
          assertNotInfinite(iter.size);
          iter.forEach(function(v, k)  {return map.set(k, v)});
        });
    }

    Map.prototype.toString = function() {
      return this.__toString('Map {', '}');
    };

    // @pragma Access

    Map.prototype.get = function(k, notSetValue) {
      return this._root ?
        this._root.get(0, undefined, k, notSetValue) :
        notSetValue;
    };

    // @pragma Modification

    Map.prototype.set = function(k, v) {
      return updateMap(this, k, v);
    };

    Map.prototype.setIn = function(keyPath, v) {
      return this.updateIn(keyPath, NOT_SET, function()  {return v});
    };

    Map.prototype.remove = function(k) {
      return updateMap(this, k, NOT_SET);
    };

    Map.prototype.deleteIn = function(keyPath) {
      return this.updateIn(keyPath, function()  {return NOT_SET});
    };

    Map.prototype.update = function(k, notSetValue, updater) {
      return arguments.length === 1 ?
        k(this) :
        this.updateIn([k], notSetValue, updater);
    };

    Map.prototype.updateIn = function(keyPath, notSetValue, updater) {
      if (!updater) {
        updater = notSetValue;
        notSetValue = undefined;
      }
      var updatedValue = updateInDeepMap(
        this,
        forceIterator(keyPath),
        notSetValue,
        updater
      );
      return updatedValue === NOT_SET ? undefined : updatedValue;
    };

    Map.prototype.clear = function() {
      if (this.size === 0) {
        return this;
      }
      if (this.__ownerID) {
        this.size = 0;
        this._root = null;
        this.__hash = undefined;
        this.__altered = true;
        return this;
      }
      return emptyMap();
    };

    // @pragma Composition

    Map.prototype.merge = function(/*...iters*/) {
      return mergeIntoMapWith(this, undefined, arguments);
    };

    Map.prototype.mergeWith = function(merger) {var iters = SLICE$0.call(arguments, 1);
      return mergeIntoMapWith(this, merger, iters);
    };

    Map.prototype.mergeIn = function(keyPath) {var iters = SLICE$0.call(arguments, 1);
      return this.updateIn(
        keyPath,
        emptyMap(),
        function(m ) {return typeof m.merge === 'function' ?
          m.merge.apply(m, iters) :
          iters[iters.length - 1]}
      );
    };

    Map.prototype.mergeDeep = function(/*...iters*/) {
      return mergeIntoMapWith(this, deepMerger, arguments);
    };

    Map.prototype.mergeDeepWith = function(merger) {var iters = SLICE$0.call(arguments, 1);
      return mergeIntoMapWith(this, deepMergerWith(merger), iters);
    };

    Map.prototype.mergeDeepIn = function(keyPath) {var iters = SLICE$0.call(arguments, 1);
      return this.updateIn(
        keyPath,
        emptyMap(),
        function(m ) {return typeof m.mergeDeep === 'function' ?
          m.mergeDeep.apply(m, iters) :
          iters[iters.length - 1]}
      );
    };

    Map.prototype.sort = function(comparator) {
      // Late binding
      return OrderedMap(sortFactory(this, comparator));
    };

    Map.prototype.sortBy = function(mapper, comparator) {
      // Late binding
      return OrderedMap(sortFactory(this, comparator, mapper));
    };

    // @pragma Mutability

    Map.prototype.withMutations = function(fn) {
      var mutable = this.asMutable();
      fn(mutable);
      return mutable.wasAltered() ? mutable.__ensureOwner(this.__ownerID) : this;
    };

    Map.prototype.asMutable = function() {
      return this.__ownerID ? this : this.__ensureOwner(new OwnerID());
    };

    Map.prototype.asImmutable = function() {
      return this.__ensureOwner();
    };

    Map.prototype.wasAltered = function() {
      return this.__altered;
    };

    Map.prototype.__iterator = function(type, reverse) {
      return new MapIterator(this, type, reverse);
    };

    Map.prototype.__iterate = function(fn, reverse) {var this$0 = this;
      var iterations = 0;
      this._root && this._root.iterate(function(entry ) {
        iterations++;
        return fn(entry[1], entry[0], this$0);
      }, reverse);
      return iterations;
    };

    Map.prototype.__ensureOwner = function(ownerID) {
      if (ownerID === this.__ownerID) {
        return this;
      }
      if (!ownerID) {
        this.__ownerID = ownerID;
        this.__altered = false;
        return this;
      }
      return makeMap(this.size, this._root, ownerID, this.__hash);
    };


  function isMap(maybeMap) {
    return !!(maybeMap && maybeMap[IS_MAP_SENTINEL]);
  }

  Map.isMap = isMap;

  var IS_MAP_SENTINEL = '@@__IMMUTABLE_MAP__@@';

  var MapPrototype = Map.prototype;
  MapPrototype[IS_MAP_SENTINEL] = true;
  MapPrototype[DELETE] = MapPrototype.remove;
  MapPrototype.removeIn = MapPrototype.deleteIn;


  // #pragma Trie Nodes



    function ArrayMapNode(ownerID, entries) {
      this.ownerID = ownerID;
      this.entries = entries;
    }

    ArrayMapNode.prototype.get = function(shift, keyHash, key, notSetValue) {
      var entries = this.entries;
      for (var ii = 0, len = entries.length; ii < len; ii++) {
        if (is(key, entries[ii][0])) {
          return entries[ii][1];
        }
      }
      return notSetValue;
    };

    ArrayMapNode.prototype.update = function(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
      var removed = value === NOT_SET;

      var entries = this.entries;
      var idx = 0;
      for (var len = entries.length; idx < len; idx++) {
        if (is(key, entries[idx][0])) {
          break;
        }
      }
      var exists = idx < len;

      if (exists ? entries[idx][1] === value : removed) {
        return this;
      }

      SetRef(didAlter);
      (removed || !exists) && SetRef(didChangeSize);

      if (removed && entries.length === 1) {
        return; // undefined
      }

      if (!exists && !removed && entries.length >= MAX_ARRAY_MAP_SIZE) {
        return createNodes(ownerID, entries, key, value);
      }

      var isEditable = ownerID && ownerID === this.ownerID;
      var newEntries = isEditable ? entries : arrCopy(entries);

      if (exists) {
        if (removed) {
          idx === len - 1 ? newEntries.pop() : (newEntries[idx] = newEntries.pop());
        } else {
          newEntries[idx] = [key, value];
        }
      } else {
        newEntries.push([key, value]);
      }

      if (isEditable) {
        this.entries = newEntries;
        return this;
      }

      return new ArrayMapNode(ownerID, newEntries);
    };




    function BitmapIndexedNode(ownerID, bitmap, nodes) {
      this.ownerID = ownerID;
      this.bitmap = bitmap;
      this.nodes = nodes;
    }

    BitmapIndexedNode.prototype.get = function(shift, keyHash, key, notSetValue) {
      if (keyHash === undefined) {
        keyHash = hash(key);
      }
      var bit = (1 << ((shift === 0 ? keyHash : keyHash >>> shift) & MASK));
      var bitmap = this.bitmap;
      return (bitmap & bit) === 0 ? notSetValue :
        this.nodes[popCount(bitmap & (bit - 1))].get(shift + SHIFT, keyHash, key, notSetValue);
    };

    BitmapIndexedNode.prototype.update = function(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
      if (keyHash === undefined) {
        keyHash = hash(key);
      }
      var keyHashFrag = (shift === 0 ? keyHash : keyHash >>> shift) & MASK;
      var bit = 1 << keyHashFrag;
      var bitmap = this.bitmap;
      var exists = (bitmap & bit) !== 0;

      if (!exists && value === NOT_SET) {
        return this;
      }

      var idx = popCount(bitmap & (bit - 1));
      var nodes = this.nodes;
      var node = exists ? nodes[idx] : undefined;
      var newNode = updateNode(node, ownerID, shift + SHIFT, keyHash, key, value, didChangeSize, didAlter);

      if (newNode === node) {
        return this;
      }

      if (!exists && newNode && nodes.length >= MAX_BITMAP_INDEXED_SIZE) {
        return expandNodes(ownerID, nodes, bitmap, keyHashFrag, newNode);
      }

      if (exists && !newNode && nodes.length === 2 && isLeafNode(nodes[idx ^ 1])) {
        return nodes[idx ^ 1];
      }

      if (exists && newNode && nodes.length === 1 && isLeafNode(newNode)) {
        return newNode;
      }

      var isEditable = ownerID && ownerID === this.ownerID;
      var newBitmap = exists ? newNode ? bitmap : bitmap ^ bit : bitmap | bit;
      var newNodes = exists ? newNode ?
        setIn(nodes, idx, newNode, isEditable) :
        spliceOut(nodes, idx, isEditable) :
        spliceIn(nodes, idx, newNode, isEditable);

      if (isEditable) {
        this.bitmap = newBitmap;
        this.nodes = newNodes;
        return this;
      }

      return new BitmapIndexedNode(ownerID, newBitmap, newNodes);
    };




    function HashArrayMapNode(ownerID, count, nodes) {
      this.ownerID = ownerID;
      this.count = count;
      this.nodes = nodes;
    }

    HashArrayMapNode.prototype.get = function(shift, keyHash, key, notSetValue) {
      if (keyHash === undefined) {
        keyHash = hash(key);
      }
      var idx = (shift === 0 ? keyHash : keyHash >>> shift) & MASK;
      var node = this.nodes[idx];
      return node ? node.get(shift + SHIFT, keyHash, key, notSetValue) : notSetValue;
    };

    HashArrayMapNode.prototype.update = function(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
      if (keyHash === undefined) {
        keyHash = hash(key);
      }
      var idx = (shift === 0 ? keyHash : keyHash >>> shift) & MASK;
      var removed = value === NOT_SET;
      var nodes = this.nodes;
      var node = nodes[idx];

      if (removed && !node) {
        return this;
      }

      var newNode = updateNode(node, ownerID, shift + SHIFT, keyHash, key, value, didChangeSize, didAlter);
      if (newNode === node) {
        return this;
      }

      var newCount = this.count;
      if (!node) {
        newCount++;
      } else if (!newNode) {
        newCount--;
        if (newCount < MIN_HASH_ARRAY_MAP_SIZE) {
          return packNodes(ownerID, nodes, newCount, idx);
        }
      }

      var isEditable = ownerID && ownerID === this.ownerID;
      var newNodes = setIn(nodes, idx, newNode, isEditable);

      if (isEditable) {
        this.count = newCount;
        this.nodes = newNodes;
        return this;
      }

      return new HashArrayMapNode(ownerID, newCount, newNodes);
    };




    function HashCollisionNode(ownerID, keyHash, entries) {
      this.ownerID = ownerID;
      this.keyHash = keyHash;
      this.entries = entries;
    }

    HashCollisionNode.prototype.get = function(shift, keyHash, key, notSetValue) {
      var entries = this.entries;
      for (var ii = 0, len = entries.length; ii < len; ii++) {
        if (is(key, entries[ii][0])) {
          return entries[ii][1];
        }
      }
      return notSetValue;
    };

    HashCollisionNode.prototype.update = function(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
      if (keyHash === undefined) {
        keyHash = hash(key);
      }

      var removed = value === NOT_SET;

      if (keyHash !== this.keyHash) {
        if (removed) {
          return this;
        }
        SetRef(didAlter);
        SetRef(didChangeSize);
        return mergeIntoNode(this, ownerID, shift, keyHash, [key, value]);
      }

      var entries = this.entries;
      var idx = 0;
      for (var len = entries.length; idx < len; idx++) {
        if (is(key, entries[idx][0])) {
          break;
        }
      }
      var exists = idx < len;

      if (exists ? entries[idx][1] === value : removed) {
        return this;
      }

      SetRef(didAlter);
      (removed || !exists) && SetRef(didChangeSize);

      if (removed && len === 2) {
        return new ValueNode(ownerID, this.keyHash, entries[idx ^ 1]);
      }

      var isEditable = ownerID && ownerID === this.ownerID;
      var newEntries = isEditable ? entries : arrCopy(entries);

      if (exists) {
        if (removed) {
          idx === len - 1 ? newEntries.pop() : (newEntries[idx] = newEntries.pop());
        } else {
          newEntries[idx] = [key, value];
        }
      } else {
        newEntries.push([key, value]);
      }

      if (isEditable) {
        this.entries = newEntries;
        return this;
      }

      return new HashCollisionNode(ownerID, this.keyHash, newEntries);
    };




    function ValueNode(ownerID, keyHash, entry) {
      this.ownerID = ownerID;
      this.keyHash = keyHash;
      this.entry = entry;
    }

    ValueNode.prototype.get = function(shift, keyHash, key, notSetValue) {
      return is(key, this.entry[0]) ? this.entry[1] : notSetValue;
    };

    ValueNode.prototype.update = function(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
      var removed = value === NOT_SET;
      var keyMatch = is(key, this.entry[0]);
      if (keyMatch ? value === this.entry[1] : removed) {
        return this;
      }

      SetRef(didAlter);

      if (removed) {
        SetRef(didChangeSize);
        return; // undefined
      }

      if (keyMatch) {
        if (ownerID && ownerID === this.ownerID) {
          this.entry[1] = value;
          return this;
        }
        return new ValueNode(ownerID, this.keyHash, [key, value]);
      }

      SetRef(didChangeSize);
      return mergeIntoNode(this, ownerID, shift, hash(key), [key, value]);
    };



  // #pragma Iterators

  ArrayMapNode.prototype.iterate =
  HashCollisionNode.prototype.iterate = function (fn, reverse) {
    var entries = this.entries;
    for (var ii = 0, maxIndex = entries.length - 1; ii <= maxIndex; ii++) {
      if (fn(entries[reverse ? maxIndex - ii : ii]) === false) {
        return false;
      }
    }
  };

  BitmapIndexedNode.prototype.iterate =
  HashArrayMapNode.prototype.iterate = function (fn, reverse) {
    var nodes = this.nodes;
    for (var ii = 0, maxIndex = nodes.length - 1; ii <= maxIndex; ii++) {
      var node = nodes[reverse ? maxIndex - ii : ii];
      if (node && node.iterate(fn, reverse) === false) {
        return false;
      }
    }
  };

  ValueNode.prototype.iterate = function (fn, reverse) {
    return fn(this.entry);
  };

  createClass(MapIterator, Iterator);

    function MapIterator(map, type, reverse) {
      this._type = type;
      this._reverse = reverse;
      this._stack = map._root && mapIteratorFrame(map._root);
    }

    MapIterator.prototype.next = function() {
      var type = this._type;
      var stack = this._stack;
      while (stack) {
        var node = stack.node;
        var index = stack.index++;
        var maxIndex;
        if (node.entry) {
          if (index === 0) {
            return mapIteratorValue(type, node.entry);
          }
        } else if (node.entries) {
          maxIndex = node.entries.length - 1;
          if (index <= maxIndex) {
            return mapIteratorValue(type, node.entries[this._reverse ? maxIndex - index : index]);
          }
        } else {
          maxIndex = node.nodes.length - 1;
          if (index <= maxIndex) {
            var subNode = node.nodes[this._reverse ? maxIndex - index : index];
            if (subNode) {
              if (subNode.entry) {
                return mapIteratorValue(type, subNode.entry);
              }
              stack = this._stack = mapIteratorFrame(subNode, stack);
            }
            continue;
          }
        }
        stack = this._stack = this._stack.__prev;
      }
      return iteratorDone();
    };


  function mapIteratorValue(type, entry) {
    return iteratorValue(type, entry[0], entry[1]);
  }

  function mapIteratorFrame(node, prev) {
    return {
      node: node,
      index: 0,
      __prev: prev
    };
  }

  function makeMap(size, root, ownerID, hash) {
    var map = Object.create(MapPrototype);
    map.size = size;
    map._root = root;
    map.__ownerID = ownerID;
    map.__hash = hash;
    map.__altered = false;
    return map;
  }

  var EMPTY_MAP;
  function emptyMap() {
    return EMPTY_MAP || (EMPTY_MAP = makeMap(0));
  }

  function updateMap(map, k, v) {
    var newRoot;
    var newSize;
    if (!map._root) {
      if (v === NOT_SET) {
        return map;
      }
      newSize = 1;
      newRoot = new ArrayMapNode(map.__ownerID, [[k, v]]);
    } else {
      var didChangeSize = MakeRef(CHANGE_LENGTH);
      var didAlter = MakeRef(DID_ALTER);
      newRoot = updateNode(map._root, map.__ownerID, 0, undefined, k, v, didChangeSize, didAlter);
      if (!didAlter.value) {
        return map;
      }
      newSize = map.size + (didChangeSize.value ? v === NOT_SET ? -1 : 1 : 0);
    }
    if (map.__ownerID) {
      map.size = newSize;
      map._root = newRoot;
      map.__hash = undefined;
      map.__altered = true;
      return map;
    }
    return newRoot ? makeMap(newSize, newRoot) : emptyMap();
  }

  function updateNode(node, ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
    if (!node) {
      if (value === NOT_SET) {
        return node;
      }
      SetRef(didAlter);
      SetRef(didChangeSize);
      return new ValueNode(ownerID, keyHash, [key, value]);
    }
    return node.update(ownerID, shift, keyHash, key, value, didChangeSize, didAlter);
  }

  function isLeafNode(node) {
    return node.constructor === ValueNode || node.constructor === HashCollisionNode;
  }

  function mergeIntoNode(node, ownerID, shift, keyHash, entry) {
    if (node.keyHash === keyHash) {
      return new HashCollisionNode(ownerID, keyHash, [node.entry, entry]);
    }

    var idx1 = (shift === 0 ? node.keyHash : node.keyHash >>> shift) & MASK;
    var idx2 = (shift === 0 ? keyHash : keyHash >>> shift) & MASK;

    var newNode;
    var nodes = idx1 === idx2 ?
      [mergeIntoNode(node, ownerID, shift + SHIFT, keyHash, entry)] :
      ((newNode = new ValueNode(ownerID, keyHash, entry)), idx1 < idx2 ? [node, newNode] : [newNode, node]);

    return new BitmapIndexedNode(ownerID, (1 << idx1) | (1 << idx2), nodes);
  }

  function createNodes(ownerID, entries, key, value) {
    if (!ownerID) {
      ownerID = new OwnerID();
    }
    var node = new ValueNode(ownerID, hash(key), [key, value]);
    for (var ii = 0; ii < entries.length; ii++) {
      var entry = entries[ii];
      node = node.update(ownerID, 0, undefined, entry[0], entry[1]);
    }
    return node;
  }

  function packNodes(ownerID, nodes, count, excluding) {
    var bitmap = 0;
    var packedII = 0;
    var packedNodes = new Array(count);
    for (var ii = 0, bit = 1, len = nodes.length; ii < len; ii++, bit <<= 1) {
      var node = nodes[ii];
      if (node !== undefined && ii !== excluding) {
        bitmap |= bit;
        packedNodes[packedII++] = node;
      }
    }
    return new BitmapIndexedNode(ownerID, bitmap, packedNodes);
  }

  function expandNodes(ownerID, nodes, bitmap, including, node) {
    var count = 0;
    var expandedNodes = new Array(SIZE);
    for (var ii = 0; bitmap !== 0; ii++, bitmap >>>= 1) {
      expandedNodes[ii] = bitmap & 1 ? nodes[count++] : undefined;
    }
    expandedNodes[including] = node;
    return new HashArrayMapNode(ownerID, count + 1, expandedNodes);
  }

  function mergeIntoMapWith(map, merger, iterables) {
    var iters = [];
    for (var ii = 0; ii < iterables.length; ii++) {
      var value = iterables[ii];
      var iter = KeyedIterable(value);
      if (!isIterable(value)) {
        iter = iter.map(function(v ) {return fromJS(v)});
      }
      iters.push(iter);
    }
    return mergeIntoCollectionWith(map, merger, iters);
  }

  function deepMerger(existing, value, key) {
    return existing && existing.mergeDeep && isIterable(value) ?
      existing.mergeDeep(value) :
      is(existing, value) ? existing : value;
  }

  function deepMergerWith(merger) {
    return function(existing, value, key)  {
      if (existing && existing.mergeDeepWith && isIterable(value)) {
        return existing.mergeDeepWith(merger, value);
      }
      var nextValue = merger(existing, value, key);
      return is(existing, nextValue) ? existing : nextValue;
    };
  }

  function mergeIntoCollectionWith(collection, merger, iters) {
    iters = iters.filter(function(x ) {return x.size !== 0});
    if (iters.length === 0) {
      return collection;
    }
    if (collection.size === 0 && !collection.__ownerID && iters.length === 1) {
      return collection.constructor(iters[0]);
    }
    return collection.withMutations(function(collection ) {
      var mergeIntoMap = merger ?
        function(value, key)  {
          collection.update(key, NOT_SET, function(existing )
            {return existing === NOT_SET ? value : merger(existing, value, key)}
          );
        } :
        function(value, key)  {
          collection.set(key, value);
        };
      for (var ii = 0; ii < iters.length; ii++) {
        iters[ii].forEach(mergeIntoMap);
      }
    });
  }

  function updateInDeepMap(existing, keyPathIter, notSetValue, updater) {
    var isNotSet = existing === NOT_SET;
    var step = keyPathIter.next();
    if (step.done) {
      var existingValue = isNotSet ? notSetValue : existing;
      var newValue = updater(existingValue);
      return newValue === existingValue ? existing : newValue;
    }
    invariant(
      isNotSet || (existing && existing.set),
      'invalid keyPath'
    );
    var key = step.value;
    var nextExisting = isNotSet ? NOT_SET : existing.get(key, NOT_SET);
    var nextUpdated = updateInDeepMap(
      nextExisting,
      keyPathIter,
      notSetValue,
      updater
    );
    return nextUpdated === nextExisting ? existing :
      nextUpdated === NOT_SET ? existing.remove(key) :
      (isNotSet ? emptyMap() : existing).set(key, nextUpdated);
  }

  function popCount(x) {
    x = x - ((x >> 1) & 0x55555555);
    x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
    x = (x + (x >> 4)) & 0x0f0f0f0f;
    x = x + (x >> 8);
    x = x + (x >> 16);
    return x & 0x7f;
  }

  function setIn(array, idx, val, canEdit) {
    var newArray = canEdit ? array : arrCopy(array);
    newArray[idx] = val;
    return newArray;
  }

  function spliceIn(array, idx, val, canEdit) {
    var newLen = array.length + 1;
    if (canEdit && idx + 1 === newLen) {
      array[idx] = val;
      return array;
    }
    var newArray = new Array(newLen);
    var after = 0;
    for (var ii = 0; ii < newLen; ii++) {
      if (ii === idx) {
        newArray[ii] = val;
        after = -1;
      } else {
        newArray[ii] = array[ii + after];
      }
    }
    return newArray;
  }

  function spliceOut(array, idx, canEdit) {
    var newLen = array.length - 1;
    if (canEdit && idx === newLen) {
      array.pop();
      return array;
    }
    var newArray = new Array(newLen);
    var after = 0;
    for (var ii = 0; ii < newLen; ii++) {
      if (ii === idx) {
        after = 1;
      }
      newArray[ii] = array[ii + after];
    }
    return newArray;
  }

  var MAX_ARRAY_MAP_SIZE = SIZE / 4;
  var MAX_BITMAP_INDEXED_SIZE = SIZE / 2;
  var MIN_HASH_ARRAY_MAP_SIZE = SIZE / 4;

  createClass(List, IndexedCollection);

    // @pragma Construction

    function List(value) {
      var empty = emptyList();
      if (value === null || value === undefined) {
        return empty;
      }
      if (isList(value)) {
        return value;
      }
      var iter = IndexedIterable(value);
      var size = iter.size;
      if (size === 0) {
        return empty;
      }
      assertNotInfinite(size);
      if (size > 0 && size < SIZE) {
        return makeList(0, size, SHIFT, null, new VNode(iter.toArray()));
      }
      return empty.withMutations(function(list ) {
        list.setSize(size);
        iter.forEach(function(v, i)  {return list.set(i, v)});
      });
    }

    List.of = function(/*...values*/) {
      return this(arguments);
    };

    List.prototype.toString = function() {
      return this.__toString('List [', ']');
    };

    // @pragma Access

    List.prototype.get = function(index, notSetValue) {
      index = wrapIndex(this, index);
      if (index >= 0 && index < this.size) {
        index += this._origin;
        var node = listNodeFor(this, index);
        return node && node.array[index & MASK];
      }
      return notSetValue;
    };

    // @pragma Modification

    List.prototype.set = function(index, value) {
      return updateList(this, index, value);
    };

    List.prototype.remove = function(index) {
      return !this.has(index) ? this :
        index === 0 ? this.shift() :
        index === this.size - 1 ? this.pop() :
        this.splice(index, 1);
    };

    List.prototype.insert = function(index, value) {
      return this.splice(index, 0, value);
    };

    List.prototype.clear = function() {
      if (this.size === 0) {
        return this;
      }
      if (this.__ownerID) {
        this.size = this._origin = this._capacity = 0;
        this._level = SHIFT;
        this._root = this._tail = null;
        this.__hash = undefined;
        this.__altered = true;
        return this;
      }
      return emptyList();
    };

    List.prototype.push = function(/*...values*/) {
      var values = arguments;
      var oldSize = this.size;
      return this.withMutations(function(list ) {
        setListBounds(list, 0, oldSize + values.length);
        for (var ii = 0; ii < values.length; ii++) {
          list.set(oldSize + ii, values[ii]);
        }
      });
    };

    List.prototype.pop = function() {
      return setListBounds(this, 0, -1);
    };

    List.prototype.unshift = function(/*...values*/) {
      var values = arguments;
      return this.withMutations(function(list ) {
        setListBounds(list, -values.length);
        for (var ii = 0; ii < values.length; ii++) {
          list.set(ii, values[ii]);
        }
      });
    };

    List.prototype.shift = function() {
      return setListBounds(this, 1);
    };

    // @pragma Composition

    List.prototype.merge = function(/*...iters*/) {
      return mergeIntoListWith(this, undefined, arguments);
    };

    List.prototype.mergeWith = function(merger) {var iters = SLICE$0.call(arguments, 1);
      return mergeIntoListWith(this, merger, iters);
    };

    List.prototype.mergeDeep = function(/*...iters*/) {
      return mergeIntoListWith(this, deepMerger, arguments);
    };

    List.prototype.mergeDeepWith = function(merger) {var iters = SLICE$0.call(arguments, 1);
      return mergeIntoListWith(this, deepMergerWith(merger), iters);
    };

    List.prototype.setSize = function(size) {
      return setListBounds(this, 0, size);
    };

    // @pragma Iteration

    List.prototype.slice = function(begin, end) {
      var size = this.size;
      if (wholeSlice(begin, end, size)) {
        return this;
      }
      return setListBounds(
        this,
        resolveBegin(begin, size),
        resolveEnd(end, size)
      );
    };

    List.prototype.__iterator = function(type, reverse) {
      var index = 0;
      var values = iterateList(this, reverse);
      return new Iterator(function()  {
        var value = values();
        return value === DONE ?
          iteratorDone() :
          iteratorValue(type, index++, value);
      });
    };

    List.prototype.__iterate = function(fn, reverse) {
      var index = 0;
      var values = iterateList(this, reverse);
      var value;
      while ((value = values()) !== DONE) {
        if (fn(value, index++, this) === false) {
          break;
        }
      }
      return index;
    };

    List.prototype.__ensureOwner = function(ownerID) {
      if (ownerID === this.__ownerID) {
        return this;
      }
      if (!ownerID) {
        this.__ownerID = ownerID;
        return this;
      }
      return makeList(this._origin, this._capacity, this._level, this._root, this._tail, ownerID, this.__hash);
    };


  function isList(maybeList) {
    return !!(maybeList && maybeList[IS_LIST_SENTINEL]);
  }

  List.isList = isList;

  var IS_LIST_SENTINEL = '@@__IMMUTABLE_LIST__@@';

  var ListPrototype = List.prototype;
  ListPrototype[IS_LIST_SENTINEL] = true;
  ListPrototype[DELETE] = ListPrototype.remove;
  ListPrototype.setIn = MapPrototype.setIn;
  ListPrototype.deleteIn =
  ListPrototype.removeIn = MapPrototype.removeIn;
  ListPrototype.update = MapPrototype.update;
  ListPrototype.updateIn = MapPrototype.updateIn;
  ListPrototype.mergeIn = MapPrototype.mergeIn;
  ListPrototype.mergeDeepIn = MapPrototype.mergeDeepIn;
  ListPrototype.withMutations = MapPrototype.withMutations;
  ListPrototype.asMutable = MapPrototype.asMutable;
  ListPrototype.asImmutable = MapPrototype.asImmutable;
  ListPrototype.wasAltered = MapPrototype.wasAltered;



    function VNode(array, ownerID) {
      this.array = array;
      this.ownerID = ownerID;
    }

    // TODO: seems like these methods are very similar

    VNode.prototype.removeBefore = function(ownerID, level, index) {
      if (index === level ? 1 << level : this.array.length === 0) {
        return this;
      }
      var originIndex = (index >>> level) & MASK;
      if (originIndex >= this.array.length) {
        return new VNode([], ownerID);
      }
      var removingFirst = originIndex === 0;
      var newChild;
      if (level > 0) {
        var oldChild = this.array[originIndex];
        newChild = oldChild && oldChild.removeBefore(ownerID, level - SHIFT, index);
        if (newChild === oldChild && removingFirst) {
          return this;
        }
      }
      if (removingFirst && !newChild) {
        return this;
      }
      var editable = editableVNode(this, ownerID);
      if (!removingFirst) {
        for (var ii = 0; ii < originIndex; ii++) {
          editable.array[ii] = undefined;
        }
      }
      if (newChild) {
        editable.array[originIndex] = newChild;
      }
      return editable;
    };

    VNode.prototype.removeAfter = function(ownerID, level, index) {
      if (index === (level ? 1 << level : 0) || this.array.length === 0) {
        return this;
      }
      var sizeIndex = ((index - 1) >>> level) & MASK;
      if (sizeIndex >= this.array.length) {
        return this;
      }

      var newChild;
      if (level > 0) {
        var oldChild = this.array[sizeIndex];
        newChild = oldChild && oldChild.removeAfter(ownerID, level - SHIFT, index);
        if (newChild === oldChild && sizeIndex === this.array.length - 1) {
          return this;
        }
      }

      var editable = editableVNode(this, ownerID);
      editable.array.splice(sizeIndex + 1);
      if (newChild) {
        editable.array[sizeIndex] = newChild;
      }
      return editable;
    };



  var DONE = {};

  function iterateList(list, reverse) {
    var left = list._origin;
    var right = list._capacity;
    var tailPos = getTailOffset(right);
    var tail = list._tail;

    return iterateNodeOrLeaf(list._root, list._level, 0);

    function iterateNodeOrLeaf(node, level, offset) {
      return level === 0 ?
        iterateLeaf(node, offset) :
        iterateNode(node, level, offset);
    }

    function iterateLeaf(node, offset) {
      var array = offset === tailPos ? tail && tail.array : node && node.array;
      var from = offset > left ? 0 : left - offset;
      var to = right - offset;
      if (to > SIZE) {
        to = SIZE;
      }
      return function()  {
        if (from === to) {
          return DONE;
        }
        var idx = reverse ? --to : from++;
        return array && array[idx];
      };
    }

    function iterateNode(node, level, offset) {
      var values;
      var array = node && node.array;
      var from = offset > left ? 0 : (left - offset) >> level;
      var to = ((right - offset) >> level) + 1;
      if (to > SIZE) {
        to = SIZE;
      }
      return function()  {
        do {
          if (values) {
            var value = values();
            if (value !== DONE) {
              return value;
            }
            values = null;
          }
          if (from === to) {
            return DONE;
          }
          var idx = reverse ? --to : from++;
          values = iterateNodeOrLeaf(
            array && array[idx], level - SHIFT, offset + (idx << level)
          );
        } while (true);
      };
    }
  }

  function makeList(origin, capacity, level, root, tail, ownerID, hash) {
    var list = Object.create(ListPrototype);
    list.size = capacity - origin;
    list._origin = origin;
    list._capacity = capacity;
    list._level = level;
    list._root = root;
    list._tail = tail;
    list.__ownerID = ownerID;
    list.__hash = hash;
    list.__altered = false;
    return list;
  }

  var EMPTY_LIST;
  function emptyList() {
    return EMPTY_LIST || (EMPTY_LIST = makeList(0, 0, SHIFT));
  }

  function updateList(list, index, value) {
    index = wrapIndex(list, index);

    if (index !== index) {
      return list;
    }

    if (index >= list.size || index < 0) {
      return list.withMutations(function(list ) {
        index < 0 ?
          setListBounds(list, index).set(0, value) :
          setListBounds(list, 0, index + 1).set(index, value);
      });
    }

    index += list._origin;

    var newTail = list._tail;
    var newRoot = list._root;
    var didAlter = MakeRef(DID_ALTER);
    if (index >= getTailOffset(list._capacity)) {
      newTail = updateVNode(newTail, list.__ownerID, 0, index, value, didAlter);
    } else {
      newRoot = updateVNode(newRoot, list.__ownerID, list._level, index, value, didAlter);
    }

    if (!didAlter.value) {
      return list;
    }

    if (list.__ownerID) {
      list._root = newRoot;
      list._tail = newTail;
      list.__hash = undefined;
      list.__altered = true;
      return list;
    }
    return makeList(list._origin, list._capacity, list._level, newRoot, newTail);
  }

  function updateVNode(node, ownerID, level, index, value, didAlter) {
    var idx = (index >>> level) & MASK;
    var nodeHas = node && idx < node.array.length;
    if (!nodeHas && value === undefined) {
      return node;
    }

    var newNode;

    if (level > 0) {
      var lowerNode = node && node.array[idx];
      var newLowerNode = updateVNode(lowerNode, ownerID, level - SHIFT, index, value, didAlter);
      if (newLowerNode === lowerNode) {
        return node;
      }
      newNode = editableVNode(node, ownerID);
      newNode.array[idx] = newLowerNode;
      return newNode;
    }

    if (nodeHas && node.array[idx] === value) {
      return node;
    }

    SetRef(didAlter);

    newNode = editableVNode(node, ownerID);
    if (value === undefined && idx === newNode.array.length - 1) {
      newNode.array.pop();
    } else {
      newNode.array[idx] = value;
    }
    return newNode;
  }

  function editableVNode(node, ownerID) {
    if (ownerID && node && ownerID === node.ownerID) {
      return node;
    }
    return new VNode(node ? node.array.slice() : [], ownerID);
  }

  function listNodeFor(list, rawIndex) {
    if (rawIndex >= getTailOffset(list._capacity)) {
      return list._tail;
    }
    if (rawIndex < 1 << (list._level + SHIFT)) {
      var node = list._root;
      var level = list._level;
      while (node && level > 0) {
        node = node.array[(rawIndex >>> level) & MASK];
        level -= SHIFT;
      }
      return node;
    }
  }

  function setListBounds(list, begin, end) {
    // Sanitize begin & end using this shorthand for ToInt32(argument)
    // http://www.ecma-international.org/ecma-262/6.0/#sec-toint32
    if (begin !== undefined) {
      begin = begin | 0;
    }
    if (end !== undefined) {
      end = end | 0;
    }
    var owner = list.__ownerID || new OwnerID();
    var oldOrigin = list._origin;
    var oldCapacity = list._capacity;
    var newOrigin = oldOrigin + begin;
    var newCapacity = end === undefined ? oldCapacity : end < 0 ? oldCapacity + end : oldOrigin + end;
    if (newOrigin === oldOrigin && newCapacity === oldCapacity) {
      return list;
    }

    // If it's going to end after it starts, it's empty.
    if (newOrigin >= newCapacity) {
      return list.clear();
    }

    var newLevel = list._level;
    var newRoot = list._root;

    // New origin might need creating a higher root.
    var offsetShift = 0;
    while (newOrigin + offsetShift < 0) {
      newRoot = new VNode(newRoot && newRoot.array.length ? [undefined, newRoot] : [], owner);
      newLevel += SHIFT;
      offsetShift += 1 << newLevel;
    }
    if (offsetShift) {
      newOrigin += offsetShift;
      oldOrigin += offsetShift;
      newCapacity += offsetShift;
      oldCapacity += offsetShift;
    }

    var oldTailOffset = getTailOffset(oldCapacity);
    var newTailOffset = getTailOffset(newCapacity);

    // New size might need creating a higher root.
    while (newTailOffset >= 1 << (newLevel + SHIFT)) {
      newRoot = new VNode(newRoot && newRoot.array.length ? [newRoot] : [], owner);
      newLevel += SHIFT;
    }

    // Locate or create the new tail.
    var oldTail = list._tail;
    var newTail = newTailOffset < oldTailOffset ?
      listNodeFor(list, newCapacity - 1) :
      newTailOffset > oldTailOffset ? new VNode([], owner) : oldTail;

    // Merge Tail into tree.
    if (oldTail && newTailOffset > oldTailOffset && newOrigin < oldCapacity && oldTail.array.length) {
      newRoot = editableVNode(newRoot, owner);
      var node = newRoot;
      for (var level = newLevel; level > SHIFT; level -= SHIFT) {
        var idx = (oldTailOffset >>> level) & MASK;
        node = node.array[idx] = editableVNode(node.array[idx], owner);
      }
      node.array[(oldTailOffset >>> SHIFT) & MASK] = oldTail;
    }

    // If the size has been reduced, there's a chance the tail needs to be trimmed.
    if (newCapacity < oldCapacity) {
      newTail = newTail && newTail.removeAfter(owner, 0, newCapacity);
    }

    // If the new origin is within the tail, then we do not need a root.
    if (newOrigin >= newTailOffset) {
      newOrigin -= newTailOffset;
      newCapacity -= newTailOffset;
      newLevel = SHIFT;
      newRoot = null;
      newTail = newTail && newTail.removeBefore(owner, 0, newOrigin);

    // Otherwise, if the root has been trimmed, garbage collect.
    } else if (newOrigin > oldOrigin || newTailOffset < oldTailOffset) {
      offsetShift = 0;

      // Identify the new top root node of the subtree of the old root.
      while (newRoot) {
        var beginIndex = (newOrigin >>> newLevel) & MASK;
        if (beginIndex !== (newTailOffset >>> newLevel) & MASK) {
          break;
        }
        if (beginIndex) {
          offsetShift += (1 << newLevel) * beginIndex;
        }
        newLevel -= SHIFT;
        newRoot = newRoot.array[beginIndex];
      }

      // Trim the new sides of the new root.
      if (newRoot && newOrigin > oldOrigin) {
        newRoot = newRoot.removeBefore(owner, newLevel, newOrigin - offsetShift);
      }
      if (newRoot && newTailOffset < oldTailOffset) {
        newRoot = newRoot.removeAfter(owner, newLevel, newTailOffset - offsetShift);
      }
      if (offsetShift) {
        newOrigin -= offsetShift;
        newCapacity -= offsetShift;
      }
    }

    if (list.__ownerID) {
      list.size = newCapacity - newOrigin;
      list._origin = newOrigin;
      list._capacity = newCapacity;
      list._level = newLevel;
      list._root = newRoot;
      list._tail = newTail;
      list.__hash = undefined;
      list.__altered = true;
      return list;
    }
    return makeList(newOrigin, newCapacity, newLevel, newRoot, newTail);
  }

  function mergeIntoListWith(list, merger, iterables) {
    var iters = [];
    var maxSize = 0;
    for (var ii = 0; ii < iterables.length; ii++) {
      var value = iterables[ii];
      var iter = IndexedIterable(value);
      if (iter.size > maxSize) {
        maxSize = iter.size;
      }
      if (!isIterable(value)) {
        iter = iter.map(function(v ) {return fromJS(v)});
      }
      iters.push(iter);
    }
    if (maxSize > list.size) {
      list = list.setSize(maxSize);
    }
    return mergeIntoCollectionWith(list, merger, iters);
  }

  function getTailOffset(size) {
    return size < SIZE ? 0 : (((size - 1) >>> SHIFT) << SHIFT);
  }

  createClass(OrderedMap, Map);

    // @pragma Construction

    function OrderedMap(value) {
      return value === null || value === undefined ? emptyOrderedMap() :
        isOrderedMap(value) ? value :
        emptyOrderedMap().withMutations(function(map ) {
          var iter = KeyedIterable(value);
          assertNotInfinite(iter.size);
          iter.forEach(function(v, k)  {return map.set(k, v)});
        });
    }

    OrderedMap.of = function(/*...values*/) {
      return this(arguments);
    };

    OrderedMap.prototype.toString = function() {
      return this.__toString('OrderedMap {', '}');
    };

    // @pragma Access

    OrderedMap.prototype.get = function(k, notSetValue) {
      var index = this._map.get(k);
      return index !== undefined ? this._list.get(index)[1] : notSetValue;
    };

    // @pragma Modification

    OrderedMap.prototype.clear = function() {
      if (this.size === 0) {
        return this;
      }
      if (this.__ownerID) {
        this.size = 0;
        this._map.clear();
        this._list.clear();
        return this;
      }
      return emptyOrderedMap();
    };

    OrderedMap.prototype.set = function(k, v) {
      return updateOrderedMap(this, k, v);
    };

    OrderedMap.prototype.remove = function(k) {
      return updateOrderedMap(this, k, NOT_SET);
    };

    OrderedMap.prototype.wasAltered = function() {
      return this._map.wasAltered() || this._list.wasAltered();
    };

    OrderedMap.prototype.__iterate = function(fn, reverse) {var this$0 = this;
      return this._list.__iterate(
        function(entry ) {return entry && fn(entry[1], entry[0], this$0)},
        reverse
      );
    };

    OrderedMap.prototype.__iterator = function(type, reverse) {
      return this._list.fromEntrySeq().__iterator(type, reverse);
    };

    OrderedMap.prototype.__ensureOwner = function(ownerID) {
      if (ownerID === this.__ownerID) {
        return this;
      }
      var newMap = this._map.__ensureOwner(ownerID);
      var newList = this._list.__ensureOwner(ownerID);
      if (!ownerID) {
        this.__ownerID = ownerID;
        this._map = newMap;
        this._list = newList;
        return this;
      }
      return makeOrderedMap(newMap, newList, ownerID, this.__hash);
    };


  function isOrderedMap(maybeOrderedMap) {
    return isMap(maybeOrderedMap) && isOrdered(maybeOrderedMap);
  }

  OrderedMap.isOrderedMap = isOrderedMap;

  OrderedMap.prototype[IS_ORDERED_SENTINEL] = true;
  OrderedMap.prototype[DELETE] = OrderedMap.prototype.remove;



  function makeOrderedMap(map, list, ownerID, hash) {
    var omap = Object.create(OrderedMap.prototype);
    omap.size = map ? map.size : 0;
    omap._map = map;
    omap._list = list;
    omap.__ownerID = ownerID;
    omap.__hash = hash;
    return omap;
  }

  var EMPTY_ORDERED_MAP;
  function emptyOrderedMap() {
    return EMPTY_ORDERED_MAP || (EMPTY_ORDERED_MAP = makeOrderedMap(emptyMap(), emptyList()));
  }

  function updateOrderedMap(omap, k, v) {
    var map = omap._map;
    var list = omap._list;
    var i = map.get(k);
    var has = i !== undefined;
    var newMap;
    var newList;
    if (v === NOT_SET) { // removed
      if (!has) {
        return omap;
      }
      if (list.size >= SIZE && list.size >= map.size * 2) {
        newList = list.filter(function(entry, idx)  {return entry !== undefined && i !== idx});
        newMap = newList.toKeyedSeq().map(function(entry ) {return entry[0]}).flip().toMap();
        if (omap.__ownerID) {
          newMap.__ownerID = newList.__ownerID = omap.__ownerID;
        }
      } else {
        newMap = map.remove(k);
        newList = i === list.size - 1 ? list.pop() : list.set(i, undefined);
      }
    } else {
      if (has) {
        if (v === list.get(i)[1]) {
          return omap;
        }
        newMap = map;
        newList = list.set(i, [k, v]);
      } else {
        newMap = map.set(k, list.size);
        newList = list.set(list.size, [k, v]);
      }
    }
    if (omap.__ownerID) {
      omap.size = newMap.size;
      omap._map = newMap;
      omap._list = newList;
      omap.__hash = undefined;
      return omap;
    }
    return makeOrderedMap(newMap, newList);
  }

  createClass(ToKeyedSequence, KeyedSeq);
    function ToKeyedSequence(indexed, useKeys) {
      this._iter = indexed;
      this._useKeys = useKeys;
      this.size = indexed.size;
    }

    ToKeyedSequence.prototype.get = function(key, notSetValue) {
      return this._iter.get(key, notSetValue);
    };

    ToKeyedSequence.prototype.has = function(key) {
      return this._iter.has(key);
    };

    ToKeyedSequence.prototype.valueSeq = function() {
      return this._iter.valueSeq();
    };

    ToKeyedSequence.prototype.reverse = function() {var this$0 = this;
      var reversedSequence = reverseFactory(this, true);
      if (!this._useKeys) {
        reversedSequence.valueSeq = function()  {return this$0._iter.toSeq().reverse()};
      }
      return reversedSequence;
    };

    ToKeyedSequence.prototype.map = function(mapper, context) {var this$0 = this;
      var mappedSequence = mapFactory(this, mapper, context);
      if (!this._useKeys) {
        mappedSequence.valueSeq = function()  {return this$0._iter.toSeq().map(mapper, context)};
      }
      return mappedSequence;
    };

    ToKeyedSequence.prototype.__iterate = function(fn, reverse) {var this$0 = this;
      var ii;
      return this._iter.__iterate(
        this._useKeys ?
          function(v, k)  {return fn(v, k, this$0)} :
          ((ii = reverse ? resolveSize(this) : 0),
            function(v ) {return fn(v, reverse ? --ii : ii++, this$0)}),
        reverse
      );
    };

    ToKeyedSequence.prototype.__iterator = function(type, reverse) {
      if (this._useKeys) {
        return this._iter.__iterator(type, reverse);
      }
      var iterator = this._iter.__iterator(ITERATE_VALUES, reverse);
      var ii = reverse ? resolveSize(this) : 0;
      return new Iterator(function()  {
        var step = iterator.next();
        return step.done ? step :
          iteratorValue(type, reverse ? --ii : ii++, step.value, step);
      });
    };

  ToKeyedSequence.prototype[IS_ORDERED_SENTINEL] = true;


  createClass(ToIndexedSequence, IndexedSeq);
    function ToIndexedSequence(iter) {
      this._iter = iter;
      this.size = iter.size;
    }

    ToIndexedSequence.prototype.includes = function(value) {
      return this._iter.includes(value);
    };

    ToIndexedSequence.prototype.__iterate = function(fn, reverse) {var this$0 = this;
      var iterations = 0;
      return this._iter.__iterate(function(v ) {return fn(v, iterations++, this$0)}, reverse);
    };

    ToIndexedSequence.prototype.__iterator = function(type, reverse) {
      var iterator = this._iter.__iterator(ITERATE_VALUES, reverse);
      var iterations = 0;
      return new Iterator(function()  {
        var step = iterator.next();
        return step.done ? step :
          iteratorValue(type, iterations++, step.value, step)
      });
    };



  createClass(ToSetSequence, SetSeq);
    function ToSetSequence(iter) {
      this._iter = iter;
      this.size = iter.size;
    }

    ToSetSequence.prototype.has = function(key) {
      return this._iter.includes(key);
    };

    ToSetSequence.prototype.__iterate = function(fn, reverse) {var this$0 = this;
      return this._iter.__iterate(function(v ) {return fn(v, v, this$0)}, reverse);
    };

    ToSetSequence.prototype.__iterator = function(type, reverse) {
      var iterator = this._iter.__iterator(ITERATE_VALUES, reverse);
      return new Iterator(function()  {
        var step = iterator.next();
        return step.done ? step :
          iteratorValue(type, step.value, step.value, step);
      });
    };



  createClass(FromEntriesSequence, KeyedSeq);
    function FromEntriesSequence(entries) {
      this._iter = entries;
      this.size = entries.size;
    }

    FromEntriesSequence.prototype.entrySeq = function() {
      return this._iter.toSeq();
    };

    FromEntriesSequence.prototype.__iterate = function(fn, reverse) {var this$0 = this;
      return this._iter.__iterate(function(entry ) {
        // Check if entry exists first so array access doesn't throw for holes
        // in the parent iteration.
        if (entry) {
          validateEntry(entry);
          var indexedIterable = isIterable(entry);
          return fn(
            indexedIterable ? entry.get(1) : entry[1],
            indexedIterable ? entry.get(0) : entry[0],
            this$0
          );
        }
      }, reverse);
    };

    FromEntriesSequence.prototype.__iterator = function(type, reverse) {
      var iterator = this._iter.__iterator(ITERATE_VALUES, reverse);
      return new Iterator(function()  {
        while (true) {
          var step = iterator.next();
          if (step.done) {
            return step;
          }
          var entry = step.value;
          // Check if entry exists first so array access doesn't throw for holes
          // in the parent iteration.
          if (entry) {
            validateEntry(entry);
            var indexedIterable = isIterable(entry);
            return iteratorValue(
              type,
              indexedIterable ? entry.get(0) : entry[0],
              indexedIterable ? entry.get(1) : entry[1],
              step
            );
          }
        }
      });
    };


  ToIndexedSequence.prototype.cacheResult =
  ToKeyedSequence.prototype.cacheResult =
  ToSetSequence.prototype.cacheResult =
  FromEntriesSequence.prototype.cacheResult =
    cacheResultThrough;


  function flipFactory(iterable) {
    var flipSequence = makeSequence(iterable);
    flipSequence._iter = iterable;
    flipSequence.size = iterable.size;
    flipSequence.flip = function()  {return iterable};
    flipSequence.reverse = function () {
      var reversedSequence = iterable.reverse.apply(this); // super.reverse()
      reversedSequence.flip = function()  {return iterable.reverse()};
      return reversedSequence;
    };
    flipSequence.has = function(key ) {return iterable.includes(key)};
    flipSequence.includes = function(key ) {return iterable.has(key)};
    flipSequence.cacheResult = cacheResultThrough;
    flipSequence.__iterateUncached = function (fn, reverse) {var this$0 = this;
      return iterable.__iterate(function(v, k)  {return fn(k, v, this$0) !== false}, reverse);
    };
    flipSequence.__iteratorUncached = function(type, reverse) {
      if (type === ITERATE_ENTRIES) {
        var iterator = iterable.__iterator(type, reverse);
        return new Iterator(function()  {
          var step = iterator.next();
          if (!step.done) {
            var k = step.value[0];
            step.value[0] = step.value[1];
            step.value[1] = k;
          }
          return step;
        });
      }
      return iterable.__iterator(
        type === ITERATE_VALUES ? ITERATE_KEYS : ITERATE_VALUES,
        reverse
      );
    };
    return flipSequence;
  }


  function mapFactory(iterable, mapper, context) {
    var mappedSequence = makeSequence(iterable);
    mappedSequence.size = iterable.size;
    mappedSequence.has = function(key ) {return iterable.has(key)};
    mappedSequence.get = function(key, notSetValue)  {
      var v = iterable.get(key, NOT_SET);
      return v === NOT_SET ?
        notSetValue :
        mapper.call(context, v, key, iterable);
    };
    mappedSequence.__iterateUncached = function (fn, reverse) {var this$0 = this;
      return iterable.__iterate(
        function(v, k, c)  {return fn(mapper.call(context, v, k, c), k, this$0) !== false},
        reverse
      );
    };
    mappedSequence.__iteratorUncached = function (type, reverse) {
      var iterator = iterable.__iterator(ITERATE_ENTRIES, reverse);
      return new Iterator(function()  {
        var step = iterator.next();
        if (step.done) {
          return step;
        }
        var entry = step.value;
        var key = entry[0];
        return iteratorValue(
          type,
          key,
          mapper.call(context, entry[1], key, iterable),
          step
        );
      });
    };
    return mappedSequence;
  }


  function reverseFactory(iterable, useKeys) {
    var reversedSequence = makeSequence(iterable);
    reversedSequence._iter = iterable;
    reversedSequence.size = iterable.size;
    reversedSequence.reverse = function()  {return iterable};
    if (iterable.flip) {
      reversedSequence.flip = function () {
        var flipSequence = flipFactory(iterable);
        flipSequence.reverse = function()  {return iterable.flip()};
        return flipSequence;
      };
    }
    reversedSequence.get = function(key, notSetValue) 
      {return iterable.get(useKeys ? key : -1 - key, notSetValue)};
    reversedSequence.has = function(key )
      {return iterable.has(useKeys ? key : -1 - key)};
    reversedSequence.includes = function(value ) {return iterable.includes(value)};
    reversedSequence.cacheResult = cacheResultThrough;
    reversedSequence.__iterate = function (fn, reverse) {var this$0 = this;
      return iterable.__iterate(function(v, k)  {return fn(v, k, this$0)}, !reverse);
    };
    reversedSequence.__iterator =
      function(type, reverse)  {return iterable.__iterator(type, !reverse)};
    return reversedSequence;
  }


  function filterFactory(iterable, predicate, context, useKeys) {
    var filterSequence = makeSequence(iterable);
    if (useKeys) {
      filterSequence.has = function(key ) {
        var v = iterable.get(key, NOT_SET);
        return v !== NOT_SET && !!predicate.call(context, v, key, iterable);
      };
      filterSequence.get = function(key, notSetValue)  {
        var v = iterable.get(key, NOT_SET);
        return v !== NOT_SET && predicate.call(context, v, key, iterable) ?
          v : notSetValue;
      };
    }
    filterSequence.__iterateUncached = function (fn, reverse) {var this$0 = this;
      var iterations = 0;
      iterable.__iterate(function(v, k, c)  {
        if (predicate.call(context, v, k, c)) {
          iterations++;
          return fn(v, useKeys ? k : iterations - 1, this$0);
        }
      }, reverse);
      return iterations;
    };
    filterSequence.__iteratorUncached = function (type, reverse) {
      var iterator = iterable.__iterator(ITERATE_ENTRIES, reverse);
      var iterations = 0;
      return new Iterator(function()  {
        while (true) {
          var step = iterator.next();
          if (step.done) {
            return step;
          }
          var entry = step.value;
          var key = entry[0];
          var value = entry[1];
          if (predicate.call(context, value, key, iterable)) {
            return iteratorValue(type, useKeys ? key : iterations++, value, step);
          }
        }
      });
    };
    return filterSequence;
  }


  function countByFactory(iterable, grouper, context) {
    var groups = Map().asMutable();
    iterable.__iterate(function(v, k)  {
      groups.update(
        grouper.call(context, v, k, iterable),
        0,
        function(a ) {return a + 1}
      );
    });
    return groups.asImmutable();
  }


  function groupByFactory(iterable, grouper, context) {
    var isKeyedIter = isKeyed(iterable);
    var groups = (isOrdered(iterable) ? OrderedMap() : Map()).asMutable();
    iterable.__iterate(function(v, k)  {
      groups.update(
        grouper.call(context, v, k, iterable),
        function(a ) {return (a = a || [], a.push(isKeyedIter ? [k, v] : v), a)}
      );
    });
    var coerce = iterableClass(iterable);
    return groups.map(function(arr ) {return reify(iterable, coerce(arr))});
  }


  function sliceFactory(iterable, begin, end, useKeys) {
    var originalSize = iterable.size;

    // Sanitize begin & end using this shorthand for ToInt32(argument)
    // http://www.ecma-international.org/ecma-262/6.0/#sec-toint32
    if (begin !== undefined) {
      begin = begin | 0;
    }
    if (end !== undefined) {
      end = end | 0;
    }

    if (wholeSlice(begin, end, originalSize)) {
      return iterable;
    }

    var resolvedBegin = resolveBegin(begin, originalSize);
    var resolvedEnd = resolveEnd(end, originalSize);

    // begin or end will be NaN if they were provided as negative numbers and
    // this iterable's size is unknown. In that case, cache first so there is
    // a known size and these do not resolve to NaN.
    if (resolvedBegin !== resolvedBegin || resolvedEnd !== resolvedEnd) {
      return sliceFactory(iterable.toSeq().cacheResult(), begin, end, useKeys);
    }

    // Note: resolvedEnd is undefined when the original sequence's length is
    // unknown and this slice did not supply an end and should contain all
    // elements after resolvedBegin.
    // In that case, resolvedSize will be NaN and sliceSize will remain undefined.
    var resolvedSize = resolvedEnd - resolvedBegin;
    var sliceSize;
    if (resolvedSize === resolvedSize) {
      sliceSize = resolvedSize < 0 ? 0 : resolvedSize;
    }

    var sliceSeq = makeSequence(iterable);

    // If iterable.size is undefined, the size of the realized sliceSeq is
    // unknown at this point unless the number of items to slice is 0
    sliceSeq.size = sliceSize === 0 ? sliceSize : iterable.size && sliceSize || undefined;

    if (!useKeys && isSeq(iterable) && sliceSize >= 0) {
      sliceSeq.get = function (index, notSetValue) {
        index = wrapIndex(this, index);
        return index >= 0 && index < sliceSize ?
          iterable.get(index + resolvedBegin, notSetValue) :
          notSetValue;
      };
    }

    sliceSeq.__iterateUncached = function(fn, reverse) {var this$0 = this;
      if (sliceSize === 0) {
        return 0;
      }
      if (reverse) {
        return this.cacheResult().__iterate(fn, reverse);
      }
      var skipped = 0;
      var isSkipping = true;
      var iterations = 0;
      iterable.__iterate(function(v, k)  {
        if (!(isSkipping && (isSkipping = skipped++ < resolvedBegin))) {
          iterations++;
          return fn(v, useKeys ? k : iterations - 1, this$0) !== false &&
                 iterations !== sliceSize;
        }
      });
      return iterations;
    };

    sliceSeq.__iteratorUncached = function(type, reverse) {
      if (sliceSize !== 0 && reverse) {
        return this.cacheResult().__iterator(type, reverse);
      }
      // Don't bother instantiating parent iterator if taking 0.
      var iterator = sliceSize !== 0 && iterable.__iterator(type, reverse);
      var skipped = 0;
      var iterations = 0;
      return new Iterator(function()  {
        while (skipped++ < resolvedBegin) {
          iterator.next();
        }
        if (++iterations > sliceSize) {
          return iteratorDone();
        }
        var step = iterator.next();
        if (useKeys || type === ITERATE_VALUES) {
          return step;
        } else if (type === ITERATE_KEYS) {
          return iteratorValue(type, iterations - 1, undefined, step);
        } else {
          return iteratorValue(type, iterations - 1, step.value[1], step);
        }
      });
    };

    return sliceSeq;
  }


  function takeWhileFactory(iterable, predicate, context) {
    var takeSequence = makeSequence(iterable);
    takeSequence.__iterateUncached = function(fn, reverse) {var this$0 = this;
      if (reverse) {
        return this.cacheResult().__iterate(fn, reverse);
      }
      var iterations = 0;
      iterable.__iterate(function(v, k, c) 
        {return predicate.call(context, v, k, c) && ++iterations && fn(v, k, this$0)}
      );
      return iterations;
    };
    takeSequence.__iteratorUncached = function(type, reverse) {var this$0 = this;
      if (reverse) {
        return this.cacheResult().__iterator(type, reverse);
      }
      var iterator = iterable.__iterator(ITERATE_ENTRIES, reverse);
      var iterating = true;
      return new Iterator(function()  {
        if (!iterating) {
          return iteratorDone();
        }
        var step = iterator.next();
        if (step.done) {
          return step;
        }
        var entry = step.value;
        var k = entry[0];
        var v = entry[1];
        if (!predicate.call(context, v, k, this$0)) {
          iterating = false;
          return iteratorDone();
        }
        return type === ITERATE_ENTRIES ? step :
          iteratorValue(type, k, v, step);
      });
    };
    return takeSequence;
  }


  function skipWhileFactory(iterable, predicate, context, useKeys) {
    var skipSequence = makeSequence(iterable);
    skipSequence.__iterateUncached = function (fn, reverse) {var this$0 = this;
      if (reverse) {
        return this.cacheResult().__iterate(fn, reverse);
      }
      var isSkipping = true;
      var iterations = 0;
      iterable.__iterate(function(v, k, c)  {
        if (!(isSkipping && (isSkipping = predicate.call(context, v, k, c)))) {
          iterations++;
          return fn(v, useKeys ? k : iterations - 1, this$0);
        }
      });
      return iterations;
    };
    skipSequence.__iteratorUncached = function(type, reverse) {var this$0 = this;
      if (reverse) {
        return this.cacheResult().__iterator(type, reverse);
      }
      var iterator = iterable.__iterator(ITERATE_ENTRIES, reverse);
      var skipping = true;
      var iterations = 0;
      return new Iterator(function()  {
        var step, k, v;
        do {
          step = iterator.next();
          if (step.done) {
            if (useKeys || type === ITERATE_VALUES) {
              return step;
            } else if (type === ITERATE_KEYS) {
              return iteratorValue(type, iterations++, undefined, step);
            } else {
              return iteratorValue(type, iterations++, step.value[1], step);
            }
          }
          var entry = step.value;
          k = entry[0];
          v = entry[1];
          skipping && (skipping = predicate.call(context, v, k, this$0));
        } while (skipping);
        return type === ITERATE_ENTRIES ? step :
          iteratorValue(type, k, v, step);
      });
    };
    return skipSequence;
  }


  function concatFactory(iterable, values) {
    var isKeyedIterable = isKeyed(iterable);
    var iters = [iterable].concat(values).map(function(v ) {
      if (!isIterable(v)) {
        v = isKeyedIterable ?
          keyedSeqFromValue(v) :
          indexedSeqFromValue(Array.isArray(v) ? v : [v]);
      } else if (isKeyedIterable) {
        v = KeyedIterable(v);
      }
      return v;
    }).filter(function(v ) {return v.size !== 0});

    if (iters.length === 0) {
      return iterable;
    }

    if (iters.length === 1) {
      var singleton = iters[0];
      if (singleton === iterable ||
          isKeyedIterable && isKeyed(singleton) ||
          isIndexed(iterable) && isIndexed(singleton)) {
        return singleton;
      }
    }

    var concatSeq = new ArraySeq(iters);
    if (isKeyedIterable) {
      concatSeq = concatSeq.toKeyedSeq();
    } else if (!isIndexed(iterable)) {
      concatSeq = concatSeq.toSetSeq();
    }
    concatSeq = concatSeq.flatten(true);
    concatSeq.size = iters.reduce(
      function(sum, seq)  {
        if (sum !== undefined) {
          var size = seq.size;
          if (size !== undefined) {
            return sum + size;
          }
        }
      },
      0
    );
    return concatSeq;
  }


  function flattenFactory(iterable, depth, useKeys) {
    var flatSequence = makeSequence(iterable);
    flatSequence.__iterateUncached = function(fn, reverse) {
      var iterations = 0;
      var stopped = false;
      function flatDeep(iter, currentDepth) {var this$0 = this;
        iter.__iterate(function(v, k)  {
          if ((!depth || currentDepth < depth) && isIterable(v)) {
            flatDeep(v, currentDepth + 1);
          } else if (fn(v, useKeys ? k : iterations++, this$0) === false) {
            stopped = true;
          }
          return !stopped;
        }, reverse);
      }
      flatDeep(iterable, 0);
      return iterations;
    };
    flatSequence.__iteratorUncached = function(type, reverse) {
      var iterator = iterable.__iterator(type, reverse);
      var stack = [];
      var iterations = 0;
      return new Iterator(function()  {
        while (iterator) {
          var step = iterator.next();
          if (step.done !== false) {
            iterator = stack.pop();
            continue;
          }
          var v = step.value;
          if (type === ITERATE_ENTRIES) {
            v = v[1];
          }
          if ((!depth || stack.length < depth) && isIterable(v)) {
            stack.push(iterator);
            iterator = v.__iterator(type, reverse);
          } else {
            return useKeys ? step : iteratorValue(type, iterations++, v, step);
          }
        }
        return iteratorDone();
      });
    };
    return flatSequence;
  }


  function flatMapFactory(iterable, mapper, context) {
    var coerce = iterableClass(iterable);
    return iterable.toSeq().map(
      function(v, k)  {return coerce(mapper.call(context, v, k, iterable))}
    ).flatten(true);
  }


  function interposeFactory(iterable, separator) {
    var interposedSequence = makeSequence(iterable);
    interposedSequence.size = iterable.size && iterable.size * 2 -1;
    interposedSequence.__iterateUncached = function(fn, reverse) {var this$0 = this;
      var iterations = 0;
      iterable.__iterate(function(v, k) 
        {return (!iterations || fn(separator, iterations++, this$0) !== false) &&
        fn(v, iterations++, this$0) !== false},
        reverse
      );
      return iterations;
    };
    interposedSequence.__iteratorUncached = function(type, reverse) {
      var iterator = iterable.__iterator(ITERATE_VALUES, reverse);
      var iterations = 0;
      var step;
      return new Iterator(function()  {
        if (!step || iterations % 2) {
          step = iterator.next();
          if (step.done) {
            return step;
          }
        }
        return iterations % 2 ?
          iteratorValue(type, iterations++, separator) :
          iteratorValue(type, iterations++, step.value, step);
      });
    };
    return interposedSequence;
  }


  function sortFactory(iterable, comparator, mapper) {
    if (!comparator) {
      comparator = defaultComparator;
    }
    var isKeyedIterable = isKeyed(iterable);
    var index = 0;
    var entries = iterable.toSeq().map(
      function(v, k)  {return [k, v, index++, mapper ? mapper(v, k, iterable) : v]}
    ).toArray();
    entries.sort(function(a, b)  {return comparator(a[3], b[3]) || a[2] - b[2]}).forEach(
      isKeyedIterable ?
      function(v, i)  { entries[i].length = 2; } :
      function(v, i)  { entries[i] = v[1]; }
    );
    return isKeyedIterable ? KeyedSeq(entries) :
      isIndexed(iterable) ? IndexedSeq(entries) :
      SetSeq(entries);
  }


  function maxFactory(iterable, comparator, mapper) {
    if (!comparator) {
      comparator = defaultComparator;
    }
    if (mapper) {
      var entry = iterable.toSeq()
        .map(function(v, k)  {return [v, mapper(v, k, iterable)]})
        .reduce(function(a, b)  {return maxCompare(comparator, a[1], b[1]) ? b : a});
      return entry && entry[0];
    } else {
      return iterable.reduce(function(a, b)  {return maxCompare(comparator, a, b) ? b : a});
    }
  }

  function maxCompare(comparator, a, b) {
    var comp = comparator(b, a);
    // b is considered the new max if the comparator declares them equal, but
    // they are not equal and b is in fact a nullish value.
    return (comp === 0 && b !== a && (b === undefined || b === null || b !== b)) || comp > 0;
  }


  function zipWithFactory(keyIter, zipper, iters) {
    var zipSequence = makeSequence(keyIter);
    zipSequence.size = new ArraySeq(iters).map(function(i ) {return i.size}).min();
    // Note: this a generic base implementation of __iterate in terms of
    // __iterator which may be more generically useful in the future.
    zipSequence.__iterate = function(fn, reverse) {
      /* generic:
      var iterator = this.__iterator(ITERATE_ENTRIES, reverse);
      var step;
      var iterations = 0;
      while (!(step = iterator.next()).done) {
        iterations++;
        if (fn(step.value[1], step.value[0], this) === false) {
          break;
        }
      }
      return iterations;
      */
      // indexed:
      var iterator = this.__iterator(ITERATE_VALUES, reverse);
      var step;
      var iterations = 0;
      while (!(step = iterator.next()).done) {
        if (fn(step.value, iterations++, this) === false) {
          break;
        }
      }
      return iterations;
    };
    zipSequence.__iteratorUncached = function(type, reverse) {
      var iterators = iters.map(function(i )
        {return (i = Iterable(i), getIterator(reverse ? i.reverse() : i))}
      );
      var iterations = 0;
      var isDone = false;
      return new Iterator(function()  {
        var steps;
        if (!isDone) {
          steps = iterators.map(function(i ) {return i.next()});
          isDone = steps.some(function(s ) {return s.done});
        }
        if (isDone) {
          return iteratorDone();
        }
        return iteratorValue(
          type,
          iterations++,
          zipper.apply(null, steps.map(function(s ) {return s.value}))
        );
      });
    };
    return zipSequence
  }


  // #pragma Helper Functions

  function reify(iter, seq) {
    return isSeq(iter) ? seq : iter.constructor(seq);
  }

  function validateEntry(entry) {
    if (entry !== Object(entry)) {
      throw new TypeError('Expected [K, V] tuple: ' + entry);
    }
  }

  function resolveSize(iter) {
    assertNotInfinite(iter.size);
    return ensureSize(iter);
  }

  function iterableClass(iterable) {
    return isKeyed(iterable) ? KeyedIterable :
      isIndexed(iterable) ? IndexedIterable :
      SetIterable;
  }

  function makeSequence(iterable) {
    return Object.create(
      (
        isKeyed(iterable) ? KeyedSeq :
        isIndexed(iterable) ? IndexedSeq :
        SetSeq
      ).prototype
    );
  }

  function cacheResultThrough() {
    if (this._iter.cacheResult) {
      this._iter.cacheResult();
      this.size = this._iter.size;
      return this;
    } else {
      return Seq.prototype.cacheResult.call(this);
    }
  }

  function defaultComparator(a, b) {
    return a > b ? 1 : a < b ? -1 : 0;
  }

  function forceIterator(keyPath) {
    var iter = getIterator(keyPath);
    if (!iter) {
      // Array might not be iterable in this environment, so we need a fallback
      // to our wrapped type.
      if (!isArrayLike(keyPath)) {
        throw new TypeError('Expected iterable or array-like: ' + keyPath);
      }
      iter = getIterator(Iterable(keyPath));
    }
    return iter;
  }

  createClass(Record, KeyedCollection);

    function Record(defaultValues, name) {
      var hasInitialized;

      var RecordType = function Record(values) {
        if (values instanceof RecordType) {
          return values;
        }
        if (!(this instanceof RecordType)) {
          return new RecordType(values);
        }
        if (!hasInitialized) {
          hasInitialized = true;
          var keys = Object.keys(defaultValues);
          setProps(RecordTypePrototype, keys);
          RecordTypePrototype.size = keys.length;
          RecordTypePrototype._name = name;
          RecordTypePrototype._keys = keys;
          RecordTypePrototype._defaultValues = defaultValues;
        }
        this._map = Map(values);
      };

      var RecordTypePrototype = RecordType.prototype = Object.create(RecordPrototype);
      RecordTypePrototype.constructor = RecordType;

      return RecordType;
    }

    Record.prototype.toString = function() {
      return this.__toString(recordName(this) + ' {', '}');
    };

    // @pragma Access

    Record.prototype.has = function(k) {
      return this._defaultValues.hasOwnProperty(k);
    };

    Record.prototype.get = function(k, notSetValue) {
      if (!this.has(k)) {
        return notSetValue;
      }
      var defaultVal = this._defaultValues[k];
      return this._map ? this._map.get(k, defaultVal) : defaultVal;
    };

    // @pragma Modification

    Record.prototype.clear = function() {
      if (this.__ownerID) {
        this._map && this._map.clear();
        return this;
      }
      var RecordType = this.constructor;
      return RecordType._empty || (RecordType._empty = makeRecord(this, emptyMap()));
    };

    Record.prototype.set = function(k, v) {
      if (!this.has(k)) {
        throw new Error('Cannot set unknown key "' + k + '" on ' + recordName(this));
      }
      var newMap = this._map && this._map.set(k, v);
      if (this.__ownerID || newMap === this._map) {
        return this;
      }
      return makeRecord(this, newMap);
    };

    Record.prototype.remove = function(k) {
      if (!this.has(k)) {
        return this;
      }
      var newMap = this._map && this._map.remove(k);
      if (this.__ownerID || newMap === this._map) {
        return this;
      }
      return makeRecord(this, newMap);
    };

    Record.prototype.wasAltered = function() {
      return this._map.wasAltered();
    };

    Record.prototype.__iterator = function(type, reverse) {var this$0 = this;
      return KeyedIterable(this._defaultValues).map(function(_, k)  {return this$0.get(k)}).__iterator(type, reverse);
    };

    Record.prototype.__iterate = function(fn, reverse) {var this$0 = this;
      return KeyedIterable(this._defaultValues).map(function(_, k)  {return this$0.get(k)}).__iterate(fn, reverse);
    };

    Record.prototype.__ensureOwner = function(ownerID) {
      if (ownerID === this.__ownerID) {
        return this;
      }
      var newMap = this._map && this._map.__ensureOwner(ownerID);
      if (!ownerID) {
        this.__ownerID = ownerID;
        this._map = newMap;
        return this;
      }
      return makeRecord(this, newMap, ownerID);
    };


  var RecordPrototype = Record.prototype;
  RecordPrototype[DELETE] = RecordPrototype.remove;
  RecordPrototype.deleteIn =
  RecordPrototype.removeIn = MapPrototype.removeIn;
  RecordPrototype.merge = MapPrototype.merge;
  RecordPrototype.mergeWith = MapPrototype.mergeWith;
  RecordPrototype.mergeIn = MapPrototype.mergeIn;
  RecordPrototype.mergeDeep = MapPrototype.mergeDeep;
  RecordPrototype.mergeDeepWith = MapPrototype.mergeDeepWith;
  RecordPrototype.mergeDeepIn = MapPrototype.mergeDeepIn;
  RecordPrototype.setIn = MapPrototype.setIn;
  RecordPrototype.update = MapPrototype.update;
  RecordPrototype.updateIn = MapPrototype.updateIn;
  RecordPrototype.withMutations = MapPrototype.withMutations;
  RecordPrototype.asMutable = MapPrototype.asMutable;
  RecordPrototype.asImmutable = MapPrototype.asImmutable;


  function makeRecord(likeRecord, map, ownerID) {
    var record = Object.create(Object.getPrototypeOf(likeRecord));
    record._map = map;
    record.__ownerID = ownerID;
    return record;
  }

  function recordName(record) {
    return record._name || record.constructor.name || 'Record';
  }

  function setProps(prototype, names) {
    try {
      names.forEach(setProp.bind(undefined, prototype));
    } catch (error) {
      // Object.defineProperty failed. Probably IE8.
    }
  }

  function setProp(prototype, name) {
    Object.defineProperty(prototype, name, {
      get: function() {
        return this.get(name);
      },
      set: function(value) {
        invariant(this.__ownerID, 'Cannot set on an immutable record.');
        this.set(name, value);
      }
    });
  }

  createClass(Set, SetCollection);

    // @pragma Construction

    function Set(value) {
      return value === null || value === undefined ? emptySet() :
        isSet(value) && !isOrdered(value) ? value :
        emptySet().withMutations(function(set ) {
          var iter = SetIterable(value);
          assertNotInfinite(iter.size);
          iter.forEach(function(v ) {return set.add(v)});
        });
    }

    Set.of = function(/*...values*/) {
      return this(arguments);
    };

    Set.fromKeys = function(value) {
      return this(KeyedIterable(value).keySeq());
    };

    Set.prototype.toString = function() {
      return this.__toString('Set {', '}');
    };

    // @pragma Access

    Set.prototype.has = function(value) {
      return this._map.has(value);
    };

    // @pragma Modification

    Set.prototype.add = function(value) {
      return updateSet(this, this._map.set(value, true));
    };

    Set.prototype.remove = function(value) {
      return updateSet(this, this._map.remove(value));
    };

    Set.prototype.clear = function() {
      return updateSet(this, this._map.clear());
    };

    // @pragma Composition

    Set.prototype.union = function() {var iters = SLICE$0.call(arguments, 0);
      iters = iters.filter(function(x ) {return x.size !== 0});
      if (iters.length === 0) {
        return this;
      }
      if (this.size === 0 && !this.__ownerID && iters.length === 1) {
        return this.constructor(iters[0]);
      }
      return this.withMutations(function(set ) {
        for (var ii = 0; ii < iters.length; ii++) {
          SetIterable(iters[ii]).forEach(function(value ) {return set.add(value)});
        }
      });
    };

    Set.prototype.intersect = function() {var iters = SLICE$0.call(arguments, 0);
      if (iters.length === 0) {
        return this;
      }
      iters = iters.map(function(iter ) {return SetIterable(iter)});
      var originalSet = this;
      return this.withMutations(function(set ) {
        originalSet.forEach(function(value ) {
          if (!iters.every(function(iter ) {return iter.includes(value)})) {
            set.remove(value);
          }
        });
      });
    };

    Set.prototype.subtract = function() {var iters = SLICE$0.call(arguments, 0);
      if (iters.length === 0) {
        return this;
      }
      iters = iters.map(function(iter ) {return SetIterable(iter)});
      var originalSet = this;
      return this.withMutations(function(set ) {
        originalSet.forEach(function(value ) {
          if (iters.some(function(iter ) {return iter.includes(value)})) {
            set.remove(value);
          }
        });
      });
    };

    Set.prototype.merge = function() {
      return this.union.apply(this, arguments);
    };

    Set.prototype.mergeWith = function(merger) {var iters = SLICE$0.call(arguments, 1);
      return this.union.apply(this, iters);
    };

    Set.prototype.sort = function(comparator) {
      // Late binding
      return OrderedSet(sortFactory(this, comparator));
    };

    Set.prototype.sortBy = function(mapper, comparator) {
      // Late binding
      return OrderedSet(sortFactory(this, comparator, mapper));
    };

    Set.prototype.wasAltered = function() {
      return this._map.wasAltered();
    };

    Set.prototype.__iterate = function(fn, reverse) {var this$0 = this;
      return this._map.__iterate(function(_, k)  {return fn(k, k, this$0)}, reverse);
    };

    Set.prototype.__iterator = function(type, reverse) {
      return this._map.map(function(_, k)  {return k}).__iterator(type, reverse);
    };

    Set.prototype.__ensureOwner = function(ownerID) {
      if (ownerID === this.__ownerID) {
        return this;
      }
      var newMap = this._map.__ensureOwner(ownerID);
      if (!ownerID) {
        this.__ownerID = ownerID;
        this._map = newMap;
        return this;
      }
      return this.__make(newMap, ownerID);
    };


  function isSet(maybeSet) {
    return !!(maybeSet && maybeSet[IS_SET_SENTINEL]);
  }

  Set.isSet = isSet;

  var IS_SET_SENTINEL = '@@__IMMUTABLE_SET__@@';

  var SetPrototype = Set.prototype;
  SetPrototype[IS_SET_SENTINEL] = true;
  SetPrototype[DELETE] = SetPrototype.remove;
  SetPrototype.mergeDeep = SetPrototype.merge;
  SetPrototype.mergeDeepWith = SetPrototype.mergeWith;
  SetPrototype.withMutations = MapPrototype.withMutations;
  SetPrototype.asMutable = MapPrototype.asMutable;
  SetPrototype.asImmutable = MapPrototype.asImmutable;

  SetPrototype.__empty = emptySet;
  SetPrototype.__make = makeSet;

  function updateSet(set, newMap) {
    if (set.__ownerID) {
      set.size = newMap.size;
      set._map = newMap;
      return set;
    }
    return newMap === set._map ? set :
      newMap.size === 0 ? set.__empty() :
      set.__make(newMap);
  }

  function makeSet(map, ownerID) {
    var set = Object.create(SetPrototype);
    set.size = map ? map.size : 0;
    set._map = map;
    set.__ownerID = ownerID;
    return set;
  }

  var EMPTY_SET;
  function emptySet() {
    return EMPTY_SET || (EMPTY_SET = makeSet(emptyMap()));
  }

  createClass(OrderedSet, Set);

    // @pragma Construction

    function OrderedSet(value) {
      return value === null || value === undefined ? emptyOrderedSet() :
        isOrderedSet(value) ? value :
        emptyOrderedSet().withMutations(function(set ) {
          var iter = SetIterable(value);
          assertNotInfinite(iter.size);
          iter.forEach(function(v ) {return set.add(v)});
        });
    }

    OrderedSet.of = function(/*...values*/) {
      return this(arguments);
    };

    OrderedSet.fromKeys = function(value) {
      return this(KeyedIterable(value).keySeq());
    };

    OrderedSet.prototype.toString = function() {
      return this.__toString('OrderedSet {', '}');
    };


  function isOrderedSet(maybeOrderedSet) {
    return isSet(maybeOrderedSet) && isOrdered(maybeOrderedSet);
  }

  OrderedSet.isOrderedSet = isOrderedSet;

  var OrderedSetPrototype = OrderedSet.prototype;
  OrderedSetPrototype[IS_ORDERED_SENTINEL] = true;

  OrderedSetPrototype.__empty = emptyOrderedSet;
  OrderedSetPrototype.__make = makeOrderedSet;

  function makeOrderedSet(map, ownerID) {
    var set = Object.create(OrderedSetPrototype);
    set.size = map ? map.size : 0;
    set._map = map;
    set.__ownerID = ownerID;
    return set;
  }

  var EMPTY_ORDERED_SET;
  function emptyOrderedSet() {
    return EMPTY_ORDERED_SET || (EMPTY_ORDERED_SET = makeOrderedSet(emptyOrderedMap()));
  }

  createClass(Stack, IndexedCollection);

    // @pragma Construction

    function Stack(value) {
      return value === null || value === undefined ? emptyStack() :
        isStack(value) ? value :
        emptyStack().unshiftAll(value);
    }

    Stack.of = function(/*...values*/) {
      return this(arguments);
    };

    Stack.prototype.toString = function() {
      return this.__toString('Stack [', ']');
    };

    // @pragma Access

    Stack.prototype.get = function(index, notSetValue) {
      var head = this._head;
      index = wrapIndex(this, index);
      while (head && index--) {
        head = head.next;
      }
      return head ? head.value : notSetValue;
    };

    Stack.prototype.peek = function() {
      return this._head && this._head.value;
    };

    // @pragma Modification

    Stack.prototype.push = function(/*...values*/) {
      if (arguments.length === 0) {
        return this;
      }
      var newSize = this.size + arguments.length;
      var head = this._head;
      for (var ii = arguments.length - 1; ii >= 0; ii--) {
        head = {
          value: arguments[ii],
          next: head
        };
      }
      if (this.__ownerID) {
        this.size = newSize;
        this._head = head;
        this.__hash = undefined;
        this.__altered = true;
        return this;
      }
      return makeStack(newSize, head);
    };

    Stack.prototype.pushAll = function(iter) {
      iter = IndexedIterable(iter);
      if (iter.size === 0) {
        return this;
      }
      assertNotInfinite(iter.size);
      var newSize = this.size;
      var head = this._head;
      iter.reverse().forEach(function(value ) {
        newSize++;
        head = {
          value: value,
          next: head
        };
      });
      if (this.__ownerID) {
        this.size = newSize;
        this._head = head;
        this.__hash = undefined;
        this.__altered = true;
        return this;
      }
      return makeStack(newSize, head);
    };

    Stack.prototype.pop = function() {
      return this.slice(1);
    };

    Stack.prototype.unshift = function(/*...values*/) {
      return this.push.apply(this, arguments);
    };

    Stack.prototype.unshiftAll = function(iter) {
      return this.pushAll(iter);
    };

    Stack.prototype.shift = function() {
      return this.pop.apply(this, arguments);
    };

    Stack.prototype.clear = function() {
      if (this.size === 0) {
        return this;
      }
      if (this.__ownerID) {
        this.size = 0;
        this._head = undefined;
        this.__hash = undefined;
        this.__altered = true;
        return this;
      }
      return emptyStack();
    };

    Stack.prototype.slice = function(begin, end) {
      if (wholeSlice(begin, end, this.size)) {
        return this;
      }
      var resolvedBegin = resolveBegin(begin, this.size);
      var resolvedEnd = resolveEnd(end, this.size);
      if (resolvedEnd !== this.size) {
        // super.slice(begin, end);
        return IndexedCollection.prototype.slice.call(this, begin, end);
      }
      var newSize = this.size - resolvedBegin;
      var head = this._head;
      while (resolvedBegin--) {
        head = head.next;
      }
      if (this.__ownerID) {
        this.size = newSize;
        this._head = head;
        this.__hash = undefined;
        this.__altered = true;
        return this;
      }
      return makeStack(newSize, head);
    };

    // @pragma Mutability

    Stack.prototype.__ensureOwner = function(ownerID) {
      if (ownerID === this.__ownerID) {
        return this;
      }
      if (!ownerID) {
        this.__ownerID = ownerID;
        this.__altered = false;
        return this;
      }
      return makeStack(this.size, this._head, ownerID, this.__hash);
    };

    // @pragma Iteration

    Stack.prototype.__iterate = function(fn, reverse) {
      if (reverse) {
        return this.reverse().__iterate(fn);
      }
      var iterations = 0;
      var node = this._head;
      while (node) {
        if (fn(node.value, iterations++, this) === false) {
          break;
        }
        node = node.next;
      }
      return iterations;
    };

    Stack.prototype.__iterator = function(type, reverse) {
      if (reverse) {
        return this.reverse().__iterator(type);
      }
      var iterations = 0;
      var node = this._head;
      return new Iterator(function()  {
        if (node) {
          var value = node.value;
          node = node.next;
          return iteratorValue(type, iterations++, value);
        }
        return iteratorDone();
      });
    };


  function isStack(maybeStack) {
    return !!(maybeStack && maybeStack[IS_STACK_SENTINEL]);
  }

  Stack.isStack = isStack;

  var IS_STACK_SENTINEL = '@@__IMMUTABLE_STACK__@@';

  var StackPrototype = Stack.prototype;
  StackPrototype[IS_STACK_SENTINEL] = true;
  StackPrototype.withMutations = MapPrototype.withMutations;
  StackPrototype.asMutable = MapPrototype.asMutable;
  StackPrototype.asImmutable = MapPrototype.asImmutable;
  StackPrototype.wasAltered = MapPrototype.wasAltered;


  function makeStack(size, head, ownerID, hash) {
    var map = Object.create(StackPrototype);
    map.size = size;
    map._head = head;
    map.__ownerID = ownerID;
    map.__hash = hash;
    map.__altered = false;
    return map;
  }

  var EMPTY_STACK;
  function emptyStack() {
    return EMPTY_STACK || (EMPTY_STACK = makeStack(0));
  }

  /**
   * Contributes additional methods to a constructor
   */
  function mixin(ctor, methods) {
    var keyCopier = function(key ) { ctor.prototype[key] = methods[key]; };
    Object.keys(methods).forEach(keyCopier);
    Object.getOwnPropertySymbols &&
      Object.getOwnPropertySymbols(methods).forEach(keyCopier);
    return ctor;
  }

  Iterable.Iterator = Iterator;

  mixin(Iterable, {

    // ### Conversion to other types

    toArray: function() {
      assertNotInfinite(this.size);
      var array = new Array(this.size || 0);
      this.valueSeq().__iterate(function(v, i)  { array[i] = v; });
      return array;
    },

    toIndexedSeq: function() {
      return new ToIndexedSequence(this);
    },

    toJS: function() {
      return this.toSeq().map(
        function(value ) {return value && typeof value.toJS === 'function' ? value.toJS() : value}
      ).__toJS();
    },

    toJSON: function() {
      return this.toSeq().map(
        function(value ) {return value && typeof value.toJSON === 'function' ? value.toJSON() : value}
      ).__toJS();
    },

    toKeyedSeq: function() {
      return new ToKeyedSequence(this, true);
    },

    toMap: function() {
      // Use Late Binding here to solve the circular dependency.
      return Map(this.toKeyedSeq());
    },

    toObject: function() {
      assertNotInfinite(this.size);
      var object = {};
      this.__iterate(function(v, k)  { object[k] = v; });
      return object;
    },

    toOrderedMap: function() {
      // Use Late Binding here to solve the circular dependency.
      return OrderedMap(this.toKeyedSeq());
    },

    toOrderedSet: function() {
      // Use Late Binding here to solve the circular dependency.
      return OrderedSet(isKeyed(this) ? this.valueSeq() : this);
    },

    toSet: function() {
      // Use Late Binding here to solve the circular dependency.
      return Set(isKeyed(this) ? this.valueSeq() : this);
    },

    toSetSeq: function() {
      return new ToSetSequence(this);
    },

    toSeq: function() {
      return isIndexed(this) ? this.toIndexedSeq() :
        isKeyed(this) ? this.toKeyedSeq() :
        this.toSetSeq();
    },

    toStack: function() {
      // Use Late Binding here to solve the circular dependency.
      return Stack(isKeyed(this) ? this.valueSeq() : this);
    },

    toList: function() {
      // Use Late Binding here to solve the circular dependency.
      return List(isKeyed(this) ? this.valueSeq() : this);
    },


    // ### Common JavaScript methods and properties

    toString: function() {
      return '[Iterable]';
    },

    __toString: function(head, tail) {
      if (this.size === 0) {
        return head + tail;
      }
      return head + ' ' + this.toSeq().map(this.__toStringMapper).join(', ') + ' ' + tail;
    },


    // ### ES6 Collection methods (ES6 Array and Map)

    concat: function() {var values = SLICE$0.call(arguments, 0);
      return reify(this, concatFactory(this, values));
    },

    includes: function(searchValue) {
      return this.some(function(value ) {return is(value, searchValue)});
    },

    entries: function() {
      return this.__iterator(ITERATE_ENTRIES);
    },

    every: function(predicate, context) {
      assertNotInfinite(this.size);
      var returnValue = true;
      this.__iterate(function(v, k, c)  {
        if (!predicate.call(context, v, k, c)) {
          returnValue = false;
          return false;
        }
      });
      return returnValue;
    },

    filter: function(predicate, context) {
      return reify(this, filterFactory(this, predicate, context, true));
    },

    find: function(predicate, context, notSetValue) {
      var entry = this.findEntry(predicate, context);
      return entry ? entry[1] : notSetValue;
    },

    findEntry: function(predicate, context) {
      var found;
      this.__iterate(function(v, k, c)  {
        if (predicate.call(context, v, k, c)) {
          found = [k, v];
          return false;
        }
      });
      return found;
    },

    findLastEntry: function(predicate, context) {
      return this.toSeq().reverse().findEntry(predicate, context);
    },

    forEach: function(sideEffect, context) {
      assertNotInfinite(this.size);
      return this.__iterate(context ? sideEffect.bind(context) : sideEffect);
    },

    join: function(separator) {
      assertNotInfinite(this.size);
      separator = separator !== undefined ? '' + separator : ',';
      var joined = '';
      var isFirst = true;
      this.__iterate(function(v ) {
        isFirst ? (isFirst = false) : (joined += separator);
        joined += v !== null && v !== undefined ? v.toString() : '';
      });
      return joined;
    },

    keys: function() {
      return this.__iterator(ITERATE_KEYS);
    },

    map: function(mapper, context) {
      return reify(this, mapFactory(this, mapper, context));
    },

    reduce: function(reducer, initialReduction, context) {
      assertNotInfinite(this.size);
      var reduction;
      var useFirst;
      if (arguments.length < 2) {
        useFirst = true;
      } else {
        reduction = initialReduction;
      }
      this.__iterate(function(v, k, c)  {
        if (useFirst) {
          useFirst = false;
          reduction = v;
        } else {
          reduction = reducer.call(context, reduction, v, k, c);
        }
      });
      return reduction;
    },

    reduceRight: function(reducer, initialReduction, context) {
      var reversed = this.toKeyedSeq().reverse();
      return reversed.reduce.apply(reversed, arguments);
    },

    reverse: function() {
      return reify(this, reverseFactory(this, true));
    },

    slice: function(begin, end) {
      return reify(this, sliceFactory(this, begin, end, true));
    },

    some: function(predicate, context) {
      return !this.every(not(predicate), context);
    },

    sort: function(comparator) {
      return reify(this, sortFactory(this, comparator));
    },

    values: function() {
      return this.__iterator(ITERATE_VALUES);
    },


    // ### More sequential methods

    butLast: function() {
      return this.slice(0, -1);
    },

    isEmpty: function() {
      return this.size !== undefined ? this.size === 0 : !this.some(function()  {return true});
    },

    count: function(predicate, context) {
      return ensureSize(
        predicate ? this.toSeq().filter(predicate, context) : this
      );
    },

    countBy: function(grouper, context) {
      return countByFactory(this, grouper, context);
    },

    equals: function(other) {
      return deepEqual(this, other);
    },

    entrySeq: function() {
      var iterable = this;
      if (iterable._cache) {
        // We cache as an entries array, so we can just return the cache!
        return new ArraySeq(iterable._cache);
      }
      var entriesSequence = iterable.toSeq().map(entryMapper).toIndexedSeq();
      entriesSequence.fromEntrySeq = function()  {return iterable.toSeq()};
      return entriesSequence;
    },

    filterNot: function(predicate, context) {
      return this.filter(not(predicate), context);
    },

    findLast: function(predicate, context, notSetValue) {
      return this.toKeyedSeq().reverse().find(predicate, context, notSetValue);
    },

    first: function() {
      return this.find(returnTrue);
    },

    flatMap: function(mapper, context) {
      return reify(this, flatMapFactory(this, mapper, context));
    },

    flatten: function(depth) {
      return reify(this, flattenFactory(this, depth, true));
    },

    fromEntrySeq: function() {
      return new FromEntriesSequence(this);
    },

    get: function(searchKey, notSetValue) {
      return this.find(function(_, key)  {return is(key, searchKey)}, undefined, notSetValue);
    },

    getIn: function(searchKeyPath, notSetValue) {
      var nested = this;
      // Note: in an ES6 environment, we would prefer:
      // for (var key of searchKeyPath) {
      var iter = forceIterator(searchKeyPath);
      var step;
      while (!(step = iter.next()).done) {
        var key = step.value;
        nested = nested && nested.get ? nested.get(key, NOT_SET) : NOT_SET;
        if (nested === NOT_SET) {
          return notSetValue;
        }
      }
      return nested;
    },

    groupBy: function(grouper, context) {
      return groupByFactory(this, grouper, context);
    },

    has: function(searchKey) {
      return this.get(searchKey, NOT_SET) !== NOT_SET;
    },

    hasIn: function(searchKeyPath) {
      return this.getIn(searchKeyPath, NOT_SET) !== NOT_SET;
    },

    isSubset: function(iter) {
      iter = typeof iter.includes === 'function' ? iter : Iterable(iter);
      return this.every(function(value ) {return iter.includes(value)});
    },

    isSuperset: function(iter) {
      iter = typeof iter.isSubset === 'function' ? iter : Iterable(iter);
      return iter.isSubset(this);
    },

    keySeq: function() {
      return this.toSeq().map(keyMapper).toIndexedSeq();
    },

    last: function() {
      return this.toSeq().reverse().first();
    },

    max: function(comparator) {
      return maxFactory(this, comparator);
    },

    maxBy: function(mapper, comparator) {
      return maxFactory(this, comparator, mapper);
    },

    min: function(comparator) {
      return maxFactory(this, comparator ? neg(comparator) : defaultNegComparator);
    },

    minBy: function(mapper, comparator) {
      return maxFactory(this, comparator ? neg(comparator) : defaultNegComparator, mapper);
    },

    rest: function() {
      return this.slice(1);
    },

    skip: function(amount) {
      return this.slice(Math.max(0, amount));
    },

    skipLast: function(amount) {
      return reify(this, this.toSeq().reverse().skip(amount).reverse());
    },

    skipWhile: function(predicate, context) {
      return reify(this, skipWhileFactory(this, predicate, context, true));
    },

    skipUntil: function(predicate, context) {
      return this.skipWhile(not(predicate), context);
    },

    sortBy: function(mapper, comparator) {
      return reify(this, sortFactory(this, comparator, mapper));
    },

    take: function(amount) {
      return this.slice(0, Math.max(0, amount));
    },

    takeLast: function(amount) {
      return reify(this, this.toSeq().reverse().take(amount).reverse());
    },

    takeWhile: function(predicate, context) {
      return reify(this, takeWhileFactory(this, predicate, context));
    },

    takeUntil: function(predicate, context) {
      return this.takeWhile(not(predicate), context);
    },

    valueSeq: function() {
      return this.toIndexedSeq();
    },


    // ### Hashable Object

    hashCode: function() {
      return this.__hash || (this.__hash = hashIterable(this));
    }


    // ### Internal

    // abstract __iterate(fn, reverse)

    // abstract __iterator(type, reverse)
  });

  // var IS_ITERABLE_SENTINEL = '@@__IMMUTABLE_ITERABLE__@@';
  // var IS_KEYED_SENTINEL = '@@__IMMUTABLE_KEYED__@@';
  // var IS_INDEXED_SENTINEL = '@@__IMMUTABLE_INDEXED__@@';
  // var IS_ORDERED_SENTINEL = '@@__IMMUTABLE_ORDERED__@@';

  var IterablePrototype = Iterable.prototype;
  IterablePrototype[IS_ITERABLE_SENTINEL] = true;
  IterablePrototype[ITERATOR_SYMBOL] = IterablePrototype.values;
  IterablePrototype.__toJS = IterablePrototype.toArray;
  IterablePrototype.__toStringMapper = quoteString;
  IterablePrototype.inspect =
  IterablePrototype.toSource = function() { return this.toString(); };
  IterablePrototype.chain = IterablePrototype.flatMap;
  IterablePrototype.contains = IterablePrototype.includes;

  // Temporary warning about using length
  (function () {
    try {
      Object.defineProperty(IterablePrototype, 'length', {
        get: function () {
          if (!Iterable.noLengthWarning) {
            var stack;
            try {
              throw new Error();
            } catch (error) {
              stack = error.stack;
            }
            if (stack.indexOf('_wrapObject') === -1) {
              console && console.warn && console.warn(
                'iterable.length has been deprecated, '+
                'use iterable.size or iterable.count(). '+
                'This warning will become a silent error in a future version. ' +
                stack
              );
              return this.size;
            }
          }
        }
      });
    } catch (e) {}
  })();



  mixin(KeyedIterable, {

    // ### More sequential methods

    flip: function() {
      return reify(this, flipFactory(this));
    },

    findKey: function(predicate, context) {
      var entry = this.findEntry(predicate, context);
      return entry && entry[0];
    },

    findLastKey: function(predicate, context) {
      return this.toSeq().reverse().findKey(predicate, context);
    },

    keyOf: function(searchValue) {
      return this.findKey(function(value ) {return is(value, searchValue)});
    },

    lastKeyOf: function(searchValue) {
      return this.findLastKey(function(value ) {return is(value, searchValue)});
    },

    mapEntries: function(mapper, context) {var this$0 = this;
      var iterations = 0;
      return reify(this,
        this.toSeq().map(
          function(v, k)  {return mapper.call(context, [k, v], iterations++, this$0)}
        ).fromEntrySeq()
      );
    },

    mapKeys: function(mapper, context) {var this$0 = this;
      return reify(this,
        this.toSeq().flip().map(
          function(k, v)  {return mapper.call(context, k, v, this$0)}
        ).flip()
      );
    }

  });

  var KeyedIterablePrototype = KeyedIterable.prototype;
  KeyedIterablePrototype[IS_KEYED_SENTINEL] = true;
  KeyedIterablePrototype[ITERATOR_SYMBOL] = IterablePrototype.entries;
  KeyedIterablePrototype.__toJS = IterablePrototype.toObject;
  KeyedIterablePrototype.__toStringMapper = function(v, k)  {return JSON.stringify(k) + ': ' + quoteString(v)};



  mixin(IndexedIterable, {

    // ### Conversion to other types

    toKeyedSeq: function() {
      return new ToKeyedSequence(this, false);
    },


    // ### ES6 Collection methods (ES6 Array and Map)

    filter: function(predicate, context) {
      return reify(this, filterFactory(this, predicate, context, false));
    },

    findIndex: function(predicate, context) {
      var entry = this.findEntry(predicate, context);
      return entry ? entry[0] : -1;
    },

    indexOf: function(searchValue) {
      var key = this.toKeyedSeq().keyOf(searchValue);
      return key === undefined ? -1 : key;
    },

    lastIndexOf: function(searchValue) {
      var key = this.toKeyedSeq().reverse().keyOf(searchValue);
      return key === undefined ? -1 : key;

      // var index =
      // return this.toSeq().reverse().indexOf(searchValue);
    },

    reverse: function() {
      return reify(this, reverseFactory(this, false));
    },

    slice: function(begin, end) {
      return reify(this, sliceFactory(this, begin, end, false));
    },

    splice: function(index, removeNum /*, ...values*/) {
      var numArgs = arguments.length;
      removeNum = Math.max(removeNum | 0, 0);
      if (numArgs === 0 || (numArgs === 2 && !removeNum)) {
        return this;
      }
      // If index is negative, it should resolve relative to the size of the
      // collection. However size may be expensive to compute if not cached, so
      // only call count() if the number is in fact negative.
      index = resolveBegin(index, index < 0 ? this.count() : this.size);
      var spliced = this.slice(0, index);
      return reify(
        this,
        numArgs === 1 ?
          spliced :
          spliced.concat(arrCopy(arguments, 2), this.slice(index + removeNum))
      );
    },


    // ### More collection methods

    findLastIndex: function(predicate, context) {
      var key = this.toKeyedSeq().findLastKey(predicate, context);
      return key === undefined ? -1 : key;
    },

    first: function() {
      return this.get(0);
    },

    flatten: function(depth) {
      return reify(this, flattenFactory(this, depth, false));
    },

    get: function(index, notSetValue) {
      index = wrapIndex(this, index);
      return (index < 0 || (this.size === Infinity ||
          (this.size !== undefined && index > this.size))) ?
        notSetValue :
        this.find(function(_, key)  {return key === index}, undefined, notSetValue);
    },

    has: function(index) {
      index = wrapIndex(this, index);
      return index >= 0 && (this.size !== undefined ?
        this.size === Infinity || index < this.size :
        this.indexOf(index) !== -1
      );
    },

    interpose: function(separator) {
      return reify(this, interposeFactory(this, separator));
    },

    interleave: function(/*...iterables*/) {
      var iterables = [this].concat(arrCopy(arguments));
      var zipped = zipWithFactory(this.toSeq(), IndexedSeq.of, iterables);
      var interleaved = zipped.flatten(true);
      if (zipped.size) {
        interleaved.size = zipped.size * iterables.length;
      }
      return reify(this, interleaved);
    },

    last: function() {
      return this.get(-1);
    },

    skipWhile: function(predicate, context) {
      return reify(this, skipWhileFactory(this, predicate, context, false));
    },

    zip: function(/*, ...iterables */) {
      var iterables = [this].concat(arrCopy(arguments));
      return reify(this, zipWithFactory(this, defaultZipper, iterables));
    },

    zipWith: function(zipper/*, ...iterables */) {
      var iterables = arrCopy(arguments);
      iterables[0] = this;
      return reify(this, zipWithFactory(this, zipper, iterables));
    }

  });

  IndexedIterable.prototype[IS_INDEXED_SENTINEL] = true;
  IndexedIterable.prototype[IS_ORDERED_SENTINEL] = true;



  mixin(SetIterable, {

    // ### ES6 Collection methods (ES6 Array and Map)

    get: function(value, notSetValue) {
      return this.has(value) ? value : notSetValue;
    },

    includes: function(value) {
      return this.has(value);
    },


    // ### More sequential methods

    keySeq: function() {
      return this.valueSeq();
    }

  });

  SetIterable.prototype.has = IterablePrototype.includes;


  // Mixin subclasses

  mixin(KeyedSeq, KeyedIterable.prototype);
  mixin(IndexedSeq, IndexedIterable.prototype);
  mixin(SetSeq, SetIterable.prototype);

  mixin(KeyedCollection, KeyedIterable.prototype);
  mixin(IndexedCollection, IndexedIterable.prototype);
  mixin(SetCollection, SetIterable.prototype);


  // #pragma Helper functions

  function keyMapper(v, k) {
    return k;
  }

  function entryMapper(v, k) {
    return [k, v];
  }

  function not(predicate) {
    return function() {
      return !predicate.apply(this, arguments);
    }
  }

  function neg(predicate) {
    return function() {
      return -predicate.apply(this, arguments);
    }
  }

  function quoteString(value) {
    return typeof value === 'string' ? JSON.stringify(value) : value;
  }

  function defaultZipper() {
    return arrCopy(arguments);
  }

  function defaultNegComparator(a, b) {
    return a < b ? 1 : a > b ? -1 : 0;
  }

  function hashIterable(iterable) {
    if (iterable.size === Infinity) {
      return 0;
    }
    var ordered = isOrdered(iterable);
    var keyed = isKeyed(iterable);
    var h = ordered ? 1 : 0;
    var size = iterable.__iterate(
      keyed ?
        ordered ?
          function(v, k)  { h = 31 * h + hashMerge(hash(v), hash(k)) | 0; } :
          function(v, k)  { h = h + hashMerge(hash(v), hash(k)) | 0; } :
        ordered ?
          function(v ) { h = 31 * h + hash(v) | 0; } :
          function(v ) { h = h + hash(v) | 0; }
    );
    return murmurHashOfSize(size, h);
  }

  function murmurHashOfSize(size, h) {
    h = imul(h, 0xCC9E2D51);
    h = imul(h << 15 | h >>> -15, 0x1B873593);
    h = imul(h << 13 | h >>> -13, 5);
    h = (h + 0xE6546B64 | 0) ^ size;
    h = imul(h ^ h >>> 16, 0x85EBCA6B);
    h = imul(h ^ h >>> 13, 0xC2B2AE35);
    h = smi(h ^ h >>> 16);
    return h;
  }

  function hashMerge(a, b) {
    return a ^ b + 0x9E3779B9 + (a << 6) + (a >> 2) | 0; // int
  }

  var Immutable = {

    Iterable: Iterable,

    Seq: Seq,
    Collection: Collection,
    Map: Map,
    OrderedMap: OrderedMap,
    List: List,
    Stack: Stack,
    Set: Set,
    OrderedSet: OrderedSet,

    Record: Record,
    Range: Range,
    Repeat: Repeat,

    is: is,
    fromJS: fromJS

  };

  return Immutable;

}));
});

function styleInject(css, ref) {
  if ( ref === void 0 ) ref = {};
  var insertAt = ref.insertAt;

  if (!css || typeof document === 'undefined') { return; }

  var head = document.head || document.getElementsByTagName('head')[0];
  var style = document.createElement('style');
  style.type = 'text/css';

  if (insertAt === 'top') {
    if (head.firstChild) {
      head.insertBefore(style, head.firstChild);
    } else {
      head.appendChild(style);
    }
  } else {
    head.appendChild(style);
  }

  if (style.styleSheet) {
    style.styleSheet.cssText = css;
  } else {
    style.appendChild(document.createTextNode(css));
  }
}

var css_248z$6 = "/**\n * Draft v0.11.7\n *\n * Copyright (c) Facebook, Inc. and its affiliates.\n *\n * This source code is licensed under the MIT license found in the\n * LICENSE file in the root directory of this source tree.\n */\n.DraftEditor-editorContainer,.DraftEditor-root,.public-DraftEditor-content{height:inherit;text-align:initial}.public-DraftEditor-content[contenteditable=true]{-webkit-user-modify:read-write-plaintext-only}.DraftEditor-root{position:relative}.DraftEditor-editorContainer{background-color:rgba(255,255,255,0);border-left:.1px solid transparent;position:relative;z-index:1}.public-DraftEditor-block{position:relative}.DraftEditor-alignLeft .public-DraftStyleDefault-block{text-align:left}.DraftEditor-alignLeft .public-DraftEditorPlaceholder-root{left:0;text-align:left}.DraftEditor-alignCenter .public-DraftStyleDefault-block{text-align:center}.DraftEditor-alignCenter .public-DraftEditorPlaceholder-root{margin:0 auto;text-align:center;width:100%}.DraftEditor-alignRight .public-DraftStyleDefault-block{text-align:right}.DraftEditor-alignRight .public-DraftEditorPlaceholder-root{right:0;text-align:right}.public-DraftEditorPlaceholder-root{color:#9197a3;position:absolute;width:100%;z-index:1}.public-DraftEditorPlaceholder-hasFocus{color:#bdc1c9}.DraftEditorPlaceholder-hidden{display:none}.public-DraftStyleDefault-block{position:relative;white-space:pre-wrap}.public-DraftStyleDefault-ltr{direction:ltr;text-align:left}.public-DraftStyleDefault-rtl{direction:rtl;text-align:right}.public-DraftStyleDefault-listLTR{direction:ltr}.public-DraftStyleDefault-listRTL{direction:rtl}.public-DraftStyleDefault-ol,.public-DraftStyleDefault-ul{margin:16px 0;padding:0}.public-DraftStyleDefault-depth0.public-DraftStyleDefault-listLTR{margin-left:1.5em}.public-DraftStyleDefault-depth0.public-DraftStyleDefault-listRTL{margin-right:1.5em}.public-DraftStyleDefault-depth1.public-DraftStyleDefault-listLTR{margin-left:3em}.public-DraftStyleDefault-depth1.public-DraftStyleDefault-listRTL{margin-right:3em}.public-DraftStyleDefault-depth2.public-DraftStyleDefault-listLTR{margin-left:4.5em}.public-DraftStyleDefault-depth2.public-DraftStyleDefault-listRTL{margin-right:4.5em}.public-DraftStyleDefault-depth3.public-DraftStyleDefault-listLTR{margin-left:6em}.public-DraftStyleDefault-depth3.public-DraftStyleDefault-listRTL{margin-right:6em}.public-DraftStyleDefault-depth4.public-DraftStyleDefault-listLTR{margin-left:7.5em}.public-DraftStyleDefault-depth4.public-DraftStyleDefault-listRTL{margin-right:7.5em}.public-DraftStyleDefault-unorderedListItem{list-style-type:square;position:relative}.public-DraftStyleDefault-unorderedListItem.public-DraftStyleDefault-depth0{list-style-type:disc}.public-DraftStyleDefault-unorderedListItem.public-DraftStyleDefault-depth1{list-style-type:circle}.public-DraftStyleDefault-orderedListItem{list-style-type:none;position:relative}.public-DraftStyleDefault-orderedListItem.public-DraftStyleDefault-listLTR:before{left:-36px;position:absolute;text-align:right;width:30px}.public-DraftStyleDefault-orderedListItem.public-DraftStyleDefault-listRTL:before{position:absolute;right:-36px;text-align:left;width:30px}.public-DraftStyleDefault-orderedListItem:before{content:counter(ol0) \". \";counter-increment:ol0}.public-DraftStyleDefault-orderedListItem.public-DraftStyleDefault-depth1:before{content:counter(ol1,lower-alpha) \". \";counter-increment:ol1}.public-DraftStyleDefault-orderedListItem.public-DraftStyleDefault-depth2:before{content:counter(ol2,lower-roman) \". \";counter-increment:ol2}.public-DraftStyleDefault-orderedListItem.public-DraftStyleDefault-depth3:before{content:counter(ol3) \". \";counter-increment:ol3}.public-DraftStyleDefault-orderedListItem.public-DraftStyleDefault-depth4:before{content:counter(ol4,lower-alpha) \". \";counter-increment:ol4}.public-DraftStyleDefault-depth0.public-DraftStyleDefault-reset{counter-reset:ol0}.public-DraftStyleDefault-depth1.public-DraftStyleDefault-reset{counter-reset:ol1}.public-DraftStyleDefault-depth2.public-DraftStyleDefault-reset{counter-reset:ol2}.public-DraftStyleDefault-depth3.public-DraftStyleDefault-reset{counter-reset:ol3}.public-DraftStyleDefault-depth4.public-DraftStyleDefault-reset{counter-reset:ol4}";
styleInject(css_248z$6);

var css_248z$5 = ".katex {\n\tfont: normal 1.21em KaTeX_Main, Times New Roman, serif;\n\tline-height: 1.2;\n\ttext-indent: 0;\n\ttext-rendering: auto;\n}\n.katex * {\n\t-ms-high-contrast-adjust: none !important;\n\tborder-color: currentColor;\n}\n.katex .katex-version::after {\n\tcontent: '0.13.18';\n}\n.katex .katex-mathml {\n\t/* Accessibility hack to only show to screen readers\n         Found at: http://a11yproject.com/posts/how-to-hide-content/ */\n\tposition: absolute;\n\tclip: rect(1px, 1px, 1px, 1px);\n\tpadding: 0;\n\tborder: 0;\n\theight: 1px;\n\twidth: 1px;\n\toverflow: hidden;\n}\n.katex .katex-html {\n\t/* \\newline is an empty block at top level, between .base elements */\n}\n.katex .katex-html > .newline {\n\tdisplay: block;\n}\n.katex .base {\n\tposition: relative;\n\tdisplay: inline-block;\n\twhite-space: nowrap;\n\twidth: -webkit-min-content;\n\twidth: -moz-min-content;\n\twidth: min-content;\n}\n.katex .strut {\n\tdisplay: inline-block;\n}\n.katex .textbf {\n\tfont-weight: bold;\n}\n.katex .textit {\n\tfont-style: italic;\n}\n.katex .textrm {\n\tfont-family: KaTeX_Main;\n}\n.katex .textsf {\n\tfont-family: KaTeX_SansSerif;\n}\n.katex .texttt {\n\tfont-family: KaTeX_Typewriter;\n}\n.katex .mathnormal {\n\tfont-family: KaTeX_Math;\n\tfont-style: italic;\n}\n.katex .mathit {\n\tfont-family: KaTeX_Main;\n\tfont-style: italic;\n}\n.katex .mathrm {\n\tfont-style: normal;\n}\n.katex .mathbf {\n\tfont-family: KaTeX_Main;\n\tfont-weight: bold;\n}\n.katex .boldsymbol {\n\tfont-family: KaTeX_Math;\n\tfont-weight: bold;\n\tfont-style: italic;\n}\n.katex .amsrm {\n\tfont-family: KaTeX_AMS;\n}\n.katex .mathbb,\n.katex .textbb {\n\tfont-family: KaTeX_AMS;\n}\n.katex .mathcal {\n\tfont-family: KaTeX_Caligraphic;\n}\n.katex .mathfrak,\n.katex .textfrak {\n\tfont-family: KaTeX_Fraktur;\n}\n.katex .mathtt {\n\tfont-family: KaTeX_Typewriter;\n}\n.katex .mathscr,\n.katex .textscr {\n\tfont-family: KaTeX_Script;\n}\n.katex .mathsf,\n.katex .textsf {\n\tfont-family: KaTeX_SansSerif;\n}\n.katex .mathboldsf,\n.katex .textboldsf {\n\tfont-family: KaTeX_SansSerif;\n\tfont-weight: bold;\n}\n.katex .mathitsf,\n.katex .textitsf {\n\tfont-family: KaTeX_SansSerif;\n\tfont-style: italic;\n}\n.katex .mainrm {\n\tfont-family: KaTeX_Main;\n\tfont-style: normal;\n}\n.katex .vlist-t {\n\tdisplay: inline-table;\n\ttable-layout: fixed;\n\tborder-collapse: collapse;\n}\n.katex .vlist-r {\n\tdisplay: table-row;\n}\n.katex .vlist {\n\tdisplay: table-cell;\n\tvertical-align: bottom;\n\tposition: relative;\n}\n.katex .vlist > span {\n\tdisplay: block;\n\theight: 0;\n\tposition: relative;\n}\n.katex .vlist > span > span {\n\tdisplay: inline-block;\n}\n.katex .vlist > span > .pstrut {\n\toverflow: hidden;\n\twidth: 0;\n}\n.katex .vlist-t2 {\n\tmargin-right: -2px;\n}\n.katex .vlist-s {\n\tdisplay: table-cell;\n\tvertical-align: bottom;\n\tfont-size: 1px;\n\twidth: 2px;\n\tmin-width: 2px;\n}\n.katex .vbox {\n\tdisplay: inline-flex;\n\tflex-direction: column;\n\talign-items: baseline;\n}\n.katex .hbox {\n\tdisplay: inline-flex;\n\tflex-direction: row;\n\twidth: 100%;\n}\n.katex .thinbox {\n\tdisplay: inline-flex;\n\tflex-direction: row;\n\twidth: 0;\n\tmax-width: 0;\n}\n.katex .msupsub {\n\ttext-align: left;\n}\n.katex .mfrac > span > span {\n\ttext-align: center;\n}\n.katex .mfrac .frac-line {\n\tdisplay: inline-block;\n\twidth: 100%;\n\tborder-bottom-style: solid;\n}\n.katex .mfrac .frac-line,\n.katex .overline .overline-line,\n.katex .underline .underline-line,\n.katex .hline,\n.katex .hdashline,\n.katex .rule {\n\tmin-height: 1px;\n}\n.katex .mspace {\n\tdisplay: inline-block;\n}\n.katex .llap,\n.katex .rlap,\n.katex .clap {\n\twidth: 0;\n\tposition: relative;\n}\n.katex .llap > .inner,\n.katex .rlap > .inner,\n.katex .clap > .inner {\n\tposition: absolute;\n}\n.katex .llap > .fix,\n.katex .rlap > .fix,\n.katex .clap > .fix {\n\tdisplay: inline-block;\n}\n.katex .llap > .inner {\n\tright: 0;\n}\n.katex .rlap > .inner,\n.katex .clap > .inner {\n\tleft: 0;\n}\n.katex .clap > .inner > span {\n\tmargin-left: -50%;\n\tmargin-right: 50%;\n}\n.katex .rule {\n\tdisplay: inline-block;\n\tborder: solid 0;\n\tposition: relative;\n}\n.katex .overline .overline-line,\n.katex .underline .underline-line,\n.katex .hline {\n\tdisplay: inline-block;\n\twidth: 100%;\n\tborder-bottom-style: solid;\n}\n.katex .hdashline {\n\tdisplay: inline-block;\n\twidth: 100%;\n\tborder-bottom-style: dashed;\n}\n.katex .sqrt > .root {\n\t/* These values are taken from the definition of `\\r@@t`,\n             `\\mkern 5mu` and `\\mkern -10mu`. */\n\tmargin-left: 0.27777778em;\n\tmargin-right: -0.55555556em;\n}\n.katex .sizing.reset-size1.size1,\n.katex .fontsize-ensurer.reset-size1.size1 {\n\tfont-size: 1em;\n}\n.katex .sizing.reset-size1.size2,\n.katex .fontsize-ensurer.reset-size1.size2 {\n\tfont-size: 1.2em;\n}\n.katex .sizing.reset-size1.size3,\n.katex .fontsize-ensurer.reset-size1.size3 {\n\tfont-size: 1.4em;\n}\n.katex .sizing.reset-size1.size4,\n.katex .fontsize-ensurer.reset-size1.size4 {\n\tfont-size: 1.6em;\n}\n.katex .sizing.reset-size1.size5,\n.katex .fontsize-ensurer.reset-size1.size5 {\n\tfont-size: 1.8em;\n}\n.katex .sizing.reset-size1.size6,\n.katex .fontsize-ensurer.reset-size1.size6 {\n\tfont-size: 2em;\n}\n.katex .sizing.reset-size1.size7,\n.katex .fontsize-ensurer.reset-size1.size7 {\n\tfont-size: 2.4em;\n}\n.katex .sizing.reset-size1.size8,\n.katex .fontsize-ensurer.reset-size1.size8 {\n\tfont-size: 2.88em;\n}\n.katex .sizing.reset-size1.size9,\n.katex .fontsize-ensurer.reset-size1.size9 {\n\tfont-size: 3.456em;\n}\n.katex .sizing.reset-size1.size10,\n.katex .fontsize-ensurer.reset-size1.size10 {\n\tfont-size: 4.148em;\n}\n.katex .sizing.reset-size1.size11,\n.katex .fontsize-ensurer.reset-size1.size11 {\n\tfont-size: 4.976em;\n}\n.katex .sizing.reset-size2.size1,\n.katex .fontsize-ensurer.reset-size2.size1 {\n\tfont-size: 0.83333333em;\n}\n.katex .sizing.reset-size2.size2,\n.katex .fontsize-ensurer.reset-size2.size2 {\n\tfont-size: 1em;\n}\n.katex .sizing.reset-size2.size3,\n.katex .fontsize-ensurer.reset-size2.size3 {\n\tfont-size: 1.16666667em;\n}\n.katex .sizing.reset-size2.size4,\n.katex .fontsize-ensurer.reset-size2.size4 {\n\tfont-size: 1.33333333em;\n}\n.katex .sizing.reset-size2.size5,\n.katex .fontsize-ensurer.reset-size2.size5 {\n\tfont-size: 1.5em;\n}\n.katex .sizing.reset-size2.size6,\n.katex .fontsize-ensurer.reset-size2.size6 {\n\tfont-size: 1.66666667em;\n}\n.katex .sizing.reset-size2.size7,\n.katex .fontsize-ensurer.reset-size2.size7 {\n\tfont-size: 2em;\n}\n.katex .sizing.reset-size2.size8,\n.katex .fontsize-ensurer.reset-size2.size8 {\n\tfont-size: 2.4em;\n}\n.katex .sizing.reset-size2.size9,\n.katex .fontsize-ensurer.reset-size2.size9 {\n\tfont-size: 2.88em;\n}\n.katex .sizing.reset-size2.size10,\n.katex .fontsize-ensurer.reset-size2.size10 {\n\tfont-size: 3.45666667em;\n}\n.katex .sizing.reset-size2.size11,\n.katex .fontsize-ensurer.reset-size2.size11 {\n\tfont-size: 4.14666667em;\n}\n.katex .sizing.reset-size3.size1,\n.katex .fontsize-ensurer.reset-size3.size1 {\n\tfont-size: 0.71428571em;\n}\n.katex .sizing.reset-size3.size2,\n.katex .fontsize-ensurer.reset-size3.size2 {\n\tfont-size: 0.85714286em;\n}\n.katex .sizing.reset-size3.size3,\n.katex .fontsize-ensurer.reset-size3.size3 {\n\tfont-size: 1em;\n}\n.katex .sizing.reset-size3.size4,\n.katex .fontsize-ensurer.reset-size3.size4 {\n\tfont-size: 1.14285714em;\n}\n.katex .sizing.reset-size3.size5,\n.katex .fontsize-ensurer.reset-size3.size5 {\n\tfont-size: 1.28571429em;\n}\n.katex .sizing.reset-size3.size6,\n.katex .fontsize-ensurer.reset-size3.size6 {\n\tfont-size: 1.42857143em;\n}\n.katex .sizing.reset-size3.size7,\n.katex .fontsize-ensurer.reset-size3.size7 {\n\tfont-size: 1.71428571em;\n}\n.katex .sizing.reset-size3.size8,\n.katex .fontsize-ensurer.reset-size3.size8 {\n\tfont-size: 2.05714286em;\n}\n.katex .sizing.reset-size3.size9,\n.katex .fontsize-ensurer.reset-size3.size9 {\n\tfont-size: 2.46857143em;\n}\n.katex .sizing.reset-size3.size10,\n.katex .fontsize-ensurer.reset-size3.size10 {\n\tfont-size: 2.96285714em;\n}\n.katex .sizing.reset-size3.size11,\n.katex .fontsize-ensurer.reset-size3.size11 {\n\tfont-size: 3.55428571em;\n}\n.katex .sizing.reset-size4.size1,\n.katex .fontsize-ensurer.reset-size4.size1 {\n\tfont-size: 0.625em;\n}\n.katex .sizing.reset-size4.size2,\n.katex .fontsize-ensurer.reset-size4.size2 {\n\tfont-size: 0.75em;\n}\n.katex .sizing.reset-size4.size3,\n.katex .fontsize-ensurer.reset-size4.size3 {\n\tfont-size: 0.875em;\n}\n.katex .sizing.reset-size4.size4,\n.katex .fontsize-ensurer.reset-size4.size4 {\n\tfont-size: 1em;\n}\n.katex .sizing.reset-size4.size5,\n.katex .fontsize-ensurer.reset-size4.size5 {\n\tfont-size: 1.125em;\n}\n.katex .sizing.reset-size4.size6,\n.katex .fontsize-ensurer.reset-size4.size6 {\n\tfont-size: 1.25em;\n}\n.katex .sizing.reset-size4.size7,\n.katex .fontsize-ensurer.reset-size4.size7 {\n\tfont-size: 1.5em;\n}\n.katex .sizing.reset-size4.size8,\n.katex .fontsize-ensurer.reset-size4.size8 {\n\tfont-size: 1.8em;\n}\n.katex .sizing.reset-size4.size9,\n.katex .fontsize-ensurer.reset-size4.size9 {\n\tfont-size: 2.16em;\n}\n.katex .sizing.reset-size4.size10,\n.katex .fontsize-ensurer.reset-size4.size10 {\n\tfont-size: 2.5925em;\n}\n.katex .sizing.reset-size4.size11,\n.katex .fontsize-ensurer.reset-size4.size11 {\n\tfont-size: 3.11em;\n}\n.katex .sizing.reset-size5.size1,\n.katex .fontsize-ensurer.reset-size5.size1 {\n\tfont-size: 0.55555556em;\n}\n.katex .sizing.reset-size5.size2,\n.katex .fontsize-ensurer.reset-size5.size2 {\n\tfont-size: 0.66666667em;\n}\n.katex .sizing.reset-size5.size3,\n.katex .fontsize-ensurer.reset-size5.size3 {\n\tfont-size: 0.77777778em;\n}\n.katex .sizing.reset-size5.size4,\n.katex .fontsize-ensurer.reset-size5.size4 {\n\tfont-size: 0.88888889em;\n}\n.katex .sizing.reset-size5.size5,\n.katex .fontsize-ensurer.reset-size5.size5 {\n\tfont-size: 1em;\n}\n.katex .sizing.reset-size5.size6,\n.katex .fontsize-ensurer.reset-size5.size6 {\n\tfont-size: 1.11111111em;\n}\n.katex .sizing.reset-size5.size7,\n.katex .fontsize-ensurer.reset-size5.size7 {\n\tfont-size: 1.33333333em;\n}\n.katex .sizing.reset-size5.size8,\n.katex .fontsize-ensurer.reset-size5.size8 {\n\tfont-size: 1.6em;\n}\n.katex .sizing.reset-size5.size9,\n.katex .fontsize-ensurer.reset-size5.size9 {\n\tfont-size: 1.92em;\n}\n.katex .sizing.reset-size5.size10,\n.katex .fontsize-ensurer.reset-size5.size10 {\n\tfont-size: 2.30444444em;\n}\n.katex .sizing.reset-size5.size11,\n.katex .fontsize-ensurer.reset-size5.size11 {\n\tfont-size: 2.76444444em;\n}\n.katex .sizing.reset-size6.size1,\n.katex .fontsize-ensurer.reset-size6.size1 {\n\tfont-size: 0.5em;\n}\n.katex .sizing.reset-size6.size2,\n.katex .fontsize-ensurer.reset-size6.size2 {\n\tfont-size: 0.6em;\n}\n.katex .sizing.reset-size6.size3,\n.katex .fontsize-ensurer.reset-size6.size3 {\n\tfont-size: 0.7em;\n}\n.katex .sizing.reset-size6.size4,\n.katex .fontsize-ensurer.reset-size6.size4 {\n\tfont-size: 0.8em;\n}\n.katex .sizing.reset-size6.size5,\n.katex .fontsize-ensurer.reset-size6.size5 {\n\tfont-size: 0.9em;\n}\n.katex .sizing.reset-size6.size6,\n.katex .fontsize-ensurer.reset-size6.size6 {\n\tfont-size: 1em;\n}\n.katex .sizing.reset-size6.size7,\n.katex .fontsize-ensurer.reset-size6.size7 {\n\tfont-size: 1.2em;\n}\n.katex .sizing.reset-size6.size8,\n.katex .fontsize-ensurer.reset-size6.size8 {\n\tfont-size: 1.44em;\n}\n.katex .sizing.reset-size6.size9,\n.katex .fontsize-ensurer.reset-size6.size9 {\n\tfont-size: 1.728em;\n}\n.katex .sizing.reset-size6.size10,\n.katex .fontsize-ensurer.reset-size6.size10 {\n\tfont-size: 2.074em;\n}\n.katex .sizing.reset-size6.size11,\n.katex .fontsize-ensurer.reset-size6.size11 {\n\tfont-size: 2.488em;\n}\n.katex .sizing.reset-size7.size1,\n.katex .fontsize-ensurer.reset-size7.size1 {\n\tfont-size: 0.41666667em;\n}\n.katex .sizing.reset-size7.size2,\n.katex .fontsize-ensurer.reset-size7.size2 {\n\tfont-size: 0.5em;\n}\n.katex .sizing.reset-size7.size3,\n.katex .fontsize-ensurer.reset-size7.size3 {\n\tfont-size: 0.58333333em;\n}\n.katex .sizing.reset-size7.size4,\n.katex .fontsize-ensurer.reset-size7.size4 {\n\tfont-size: 0.66666667em;\n}\n.katex .sizing.reset-size7.size5,\n.katex .fontsize-ensurer.reset-size7.size5 {\n\tfont-size: 0.75em;\n}\n.katex .sizing.reset-size7.size6,\n.katex .fontsize-ensurer.reset-size7.size6 {\n\tfont-size: 0.83333333em;\n}\n.katex .sizing.reset-size7.size7,\n.katex .fontsize-ensurer.reset-size7.size7 {\n\tfont-size: 1em;\n}\n.katex .sizing.reset-size7.size8,\n.katex .fontsize-ensurer.reset-size7.size8 {\n\tfont-size: 1.2em;\n}\n.katex .sizing.reset-size7.size9,\n.katex .fontsize-ensurer.reset-size7.size9 {\n\tfont-size: 1.44em;\n}\n.katex .sizing.reset-size7.size10,\n.katex .fontsize-ensurer.reset-size7.size10 {\n\tfont-size: 1.72833333em;\n}\n.katex .sizing.reset-size7.size11,\n.katex .fontsize-ensurer.reset-size7.size11 {\n\tfont-size: 2.07333333em;\n}\n.katex .sizing.reset-size8.size1,\n.katex .fontsize-ensurer.reset-size8.size1 {\n\tfont-size: 0.34722222em;\n}\n.katex .sizing.reset-size8.size2,\n.katex .fontsize-ensurer.reset-size8.size2 {\n\tfont-size: 0.41666667em;\n}\n.katex .sizing.reset-size8.size3,\n.katex .fontsize-ensurer.reset-size8.size3 {\n\tfont-size: 0.48611111em;\n}\n.katex .sizing.reset-size8.size4,\n.katex .fontsize-ensurer.reset-size8.size4 {\n\tfont-size: 0.55555556em;\n}\n.katex .sizing.reset-size8.size5,\n.katex .fontsize-ensurer.reset-size8.size5 {\n\tfont-size: 0.625em;\n}\n.katex .sizing.reset-size8.size6,\n.katex .fontsize-ensurer.reset-size8.size6 {\n\tfont-size: 0.69444444em;\n}\n.katex .sizing.reset-size8.size7,\n.katex .fontsize-ensurer.reset-size8.size7 {\n\tfont-size: 0.83333333em;\n}\n.katex .sizing.reset-size8.size8,\n.katex .fontsize-ensurer.reset-size8.size8 {\n\tfont-size: 1em;\n}\n.katex .sizing.reset-size8.size9,\n.katex .fontsize-ensurer.reset-size8.size9 {\n\tfont-size: 1.2em;\n}\n.katex .sizing.reset-size8.size10,\n.katex .fontsize-ensurer.reset-size8.size10 {\n\tfont-size: 1.44027778em;\n}\n.katex .sizing.reset-size8.size11,\n.katex .fontsize-ensurer.reset-size8.size11 {\n\tfont-size: 1.72777778em;\n}\n.katex .sizing.reset-size9.size1,\n.katex .fontsize-ensurer.reset-size9.size1 {\n\tfont-size: 0.28935185em;\n}\n.katex .sizing.reset-size9.size2,\n.katex .fontsize-ensurer.reset-size9.size2 {\n\tfont-size: 0.34722222em;\n}\n.katex .sizing.reset-size9.size3,\n.katex .fontsize-ensurer.reset-size9.size3 {\n\tfont-size: 0.40509259em;\n}\n.katex .sizing.reset-size9.size4,\n.katex .fontsize-ensurer.reset-size9.size4 {\n\tfont-size: 0.46296296em;\n}\n.katex .sizing.reset-size9.size5,\n.katex .fontsize-ensurer.reset-size9.size5 {\n\tfont-size: 0.52083333em;\n}\n.katex .sizing.reset-size9.size6,\n.katex .fontsize-ensurer.reset-size9.size6 {\n\tfont-size: 0.5787037em;\n}\n.katex .sizing.reset-size9.size7,\n.katex .fontsize-ensurer.reset-size9.size7 {\n\tfont-size: 0.69444444em;\n}\n.katex .sizing.reset-size9.size8,\n.katex .fontsize-ensurer.reset-size9.size8 {\n\tfont-size: 0.83333333em;\n}\n.katex .sizing.reset-size9.size9,\n.katex .fontsize-ensurer.reset-size9.size9 {\n\tfont-size: 1em;\n}\n.katex .sizing.reset-size9.size10,\n.katex .fontsize-ensurer.reset-size9.size10 {\n\tfont-size: 1.20023148em;\n}\n.katex .sizing.reset-size9.size11,\n.katex .fontsize-ensurer.reset-size9.size11 {\n\tfont-size: 1.43981481em;\n}\n.katex .sizing.reset-size10.size1,\n.katex .fontsize-ensurer.reset-size10.size1 {\n\tfont-size: 0.24108004em;\n}\n.katex .sizing.reset-size10.size2,\n.katex .fontsize-ensurer.reset-size10.size2 {\n\tfont-size: 0.28929605em;\n}\n.katex .sizing.reset-size10.size3,\n.katex .fontsize-ensurer.reset-size10.size3 {\n\tfont-size: 0.33751205em;\n}\n.katex .sizing.reset-size10.size4,\n.katex .fontsize-ensurer.reset-size10.size4 {\n\tfont-size: 0.38572806em;\n}\n.katex .sizing.reset-size10.size5,\n.katex .fontsize-ensurer.reset-size10.size5 {\n\tfont-size: 0.43394407em;\n}\n.katex .sizing.reset-size10.size6,\n.katex .fontsize-ensurer.reset-size10.size6 {\n\tfont-size: 0.48216008em;\n}\n.katex .sizing.reset-size10.size7,\n.katex .fontsize-ensurer.reset-size10.size7 {\n\tfont-size: 0.57859209em;\n}\n.katex .sizing.reset-size10.size8,\n.katex .fontsize-ensurer.reset-size10.size8 {\n\tfont-size: 0.69431051em;\n}\n.katex .sizing.reset-size10.size9,\n.katex .fontsize-ensurer.reset-size10.size9 {\n\tfont-size: 0.83317261em;\n}\n.katex .sizing.reset-size10.size10,\n.katex .fontsize-ensurer.reset-size10.size10 {\n\tfont-size: 1em;\n}\n.katex .sizing.reset-size10.size11,\n.katex .fontsize-ensurer.reset-size10.size11 {\n\tfont-size: 1.19961427em;\n}\n.katex .sizing.reset-size11.size1,\n.katex .fontsize-ensurer.reset-size11.size1 {\n\tfont-size: 0.20096463em;\n}\n.katex .sizing.reset-size11.size2,\n.katex .fontsize-ensurer.reset-size11.size2 {\n\tfont-size: 0.24115756em;\n}\n.katex .sizing.reset-size11.size3,\n.katex .fontsize-ensurer.reset-size11.size3 {\n\tfont-size: 0.28135048em;\n}\n.katex .sizing.reset-size11.size4,\n.katex .fontsize-ensurer.reset-size11.size4 {\n\tfont-size: 0.32154341em;\n}\n.katex .sizing.reset-size11.size5,\n.katex .fontsize-ensurer.reset-size11.size5 {\n\tfont-size: 0.36173633em;\n}\n.katex .sizing.reset-size11.size6,\n.katex .fontsize-ensurer.reset-size11.size6 {\n\tfont-size: 0.40192926em;\n}\n.katex .sizing.reset-size11.size7,\n.katex .fontsize-ensurer.reset-size11.size7 {\n\tfont-size: 0.48231511em;\n}\n.katex .sizing.reset-size11.size8,\n.katex .fontsize-ensurer.reset-size11.size8 {\n\tfont-size: 0.57877814em;\n}\n.katex .sizing.reset-size11.size9,\n.katex .fontsize-ensurer.reset-size11.size9 {\n\tfont-size: 0.69453376em;\n}\n.katex .sizing.reset-size11.size10,\n.katex .fontsize-ensurer.reset-size11.size10 {\n\tfont-size: 0.83360129em;\n}\n.katex .sizing.reset-size11.size11,\n.katex .fontsize-ensurer.reset-size11.size11 {\n\tfont-size: 1em;\n}\n.katex .delimsizing.size1 {\n\tfont-family: KaTeX_Size1;\n}\n.katex .delimsizing.size2 {\n\tfont-family: KaTeX_Size2;\n}\n.katex .delimsizing.size3 {\n\tfont-family: KaTeX_Size3;\n}\n.katex .delimsizing.size4 {\n\tfont-family: KaTeX_Size4;\n}\n.katex .delimsizing.mult .delim-size1 > span {\n\tfont-family: KaTeX_Size1;\n}\n.katex .delimsizing.mult .delim-size4 > span {\n\tfont-family: KaTeX_Size4;\n}\n.katex .nulldelimiter {\n\tdisplay: inline-block;\n\twidth: 0.12em;\n}\n.katex .delimcenter {\n\tposition: relative;\n}\n.katex .op-symbol {\n\tposition: relative;\n}\n.katex .op-symbol.small-op {\n\tfont-family: KaTeX_Size1;\n}\n.katex .op-symbol.large-op {\n\tfont-family: KaTeX_Size2;\n}\n.katex .op-limits > .vlist-t {\n\ttext-align: center;\n}\n.katex .accent > .vlist-t {\n\ttext-align: center;\n}\n.katex .accent .accent-body {\n\tposition: relative;\n}\n.katex .accent .accent-body:not(.accent-full) {\n\twidth: 0;\n}\n.katex .overlay {\n\tdisplay: block;\n}\n.katex .mtable .vertical-separator {\n\tdisplay: inline-block;\n\tmin-width: 1px;\n}\n.katex .mtable .arraycolsep {\n\tdisplay: inline-block;\n}\n.katex .mtable .col-align-c > .vlist-t {\n\ttext-align: center;\n}\n.katex .mtable .col-align-l > .vlist-t {\n\ttext-align: left;\n}\n.katex .mtable .col-align-r > .vlist-t {\n\ttext-align: right;\n}\n.katex .svg-align {\n\ttext-align: left;\n}\n.katex svg {\n\tdisplay: block;\n\tposition: absolute;\n\twidth: 100%;\n\theight: inherit;\n\tfill: currentColor;\n\tstroke: currentColor;\n\tfill-rule: nonzero;\n\tfill-opacity: 1;\n\tstroke-width: 1;\n\tstroke-linecap: butt;\n\tstroke-linejoin: miter;\n\tstroke-miterlimit: 4;\n\tstroke-dasharray: none;\n\tstroke-dashoffset: 0;\n\tstroke-opacity: 1;\n}\n.katex svg path {\n\tstroke: none;\n}\n.katex img {\n\tborder-style: none;\n\tmin-width: 0;\n\tmin-height: 0;\n\tmax-width: none;\n\tmax-height: none;\n}\n.katex .stretchy {\n\twidth: 100%;\n\tdisplay: block;\n\tposition: relative;\n\toverflow: hidden;\n}\n.katex .stretchy::before,\n.katex .stretchy::after {\n\tcontent: '';\n}\n.katex .hide-tail {\n\twidth: 100%;\n\tposition: relative;\n\toverflow: hidden;\n}\n.katex .halfarrow-left {\n\tposition: absolute;\n\tleft: 0;\n\twidth: 50.2%;\n\toverflow: hidden;\n}\n.katex .halfarrow-right {\n\tposition: absolute;\n\tright: 0;\n\twidth: 50.2%;\n\toverflow: hidden;\n}\n.katex .brace-left {\n\tposition: absolute;\n\tleft: 0;\n\twidth: 25.1%;\n\toverflow: hidden;\n}\n.katex .brace-center {\n\tposition: absolute;\n\tleft: 25%;\n\twidth: 50%;\n\toverflow: hidden;\n}\n.katex .brace-right {\n\tposition: absolute;\n\tright: 0;\n\twidth: 25.1%;\n\toverflow: hidden;\n}\n.katex .x-arrow-pad {\n\tpadding: 0 0.5em;\n}\n.katex .cd-arrow-pad {\n\tpadding: 0 0.55556em 0 0.27778em;\n}\n.katex .x-arrow,\n.katex .mover,\n.katex .munder {\n\ttext-align: center;\n}\n.katex .boxpad {\n\tpadding: 0 0.3em 0 0.3em;\n}\n.katex .fbox,\n.katex .fcolorbox {\n\tbox-sizing: border-box;\n\tborder: 0.04em solid;\n}\n.katex .cancel-pad {\n\tpadding: 0 0.2em 0 0.2em;\n}\n.katex .cancel-lap {\n\tmargin-left: -0.2em;\n\tmargin-right: -0.2em;\n}\n.katex .sout {\n\tborder-bottom-style: solid;\n\tborder-bottom-width: 0.08em;\n}\n.katex .angl {\n\tbox-sizing: border-box;\n\tborder-top: 0.049em solid;\n\tborder-right: 0.049em solid;\n\tmargin-right: 0.03889em;\n}\n.katex .anglpad {\n\tpadding: 0 0.03889em 0 0.03889em;\n}\n.katex .eqn-num::before {\n\tcounter-increment: katexEqnNo;\n\tcontent: '(' counter(katexEqnNo) ')';\n}\n.katex .mml-eqn-num::before {\n\tcounter-increment: mmlEqnNo;\n\tcontent: '(' counter(mmlEqnNo) ')';\n}\n.katex .mtr-glue {\n\twidth: 50%;\n}\n.katex .cd-vert-arrow {\n\tdisplay: inline-block;\n\tposition: relative;\n}\n.katex .cd-label-left {\n\tdisplay: inline-block;\n\tposition: absolute;\n\tright: calc(50% + 0.3em);\n\ttext-align: left;\n}\n.katex .cd-label-right {\n\tdisplay: inline-block;\n\tposition: absolute;\n\tleft: calc(50% + 0.3em);\n\ttext-align: right;\n}\n.katex-display {\n\tdisplay: block;\n\tmargin: 1em 0;\n\ttext-align: center;\n}\n.katex-display > .katex {\n\tdisplay: block;\n\ttext-align: center;\n\twhite-space: nowrap;\n}\n.katex-display > .katex > .katex-html {\n\tdisplay: block;\n\tposition: relative;\n}\n.katex-display > .katex > .katex-html > .tag {\n\tposition: absolute;\n\tright: 0;\n}\n.katex-display.leqno > .katex > .katex-html > .tag {\n\tleft: 0;\n\tright: auto;\n}\n.katex-display.fleqn > .katex {\n\ttext-align: left;\n\tpadding-left: 2em;\n}\nbody {\n\tcounter-reset: katexEqnNo mmlEqnNo;\n}\n";
styleInject(css_248z$5);

var css_248z$4 = "@font-face {\n\tfont-family: 'KaTeX_AMS';\n\tsrc: url(/fonts/KaTeX_AMS-Regular.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_AMS-Regular.woff) format('woff'),\n\t\turl(/fonts/KaTeX_AMS-Regular.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_Caligraphic';\n\tsrc: url(/fonts/KaTeX_Caligraphic-Bold.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Caligraphic-Bold.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Caligraphic-Bold.ttf) format('truetype');\n\tfont-weight: bold;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_Caligraphic';\n\tsrc: url(/fonts/KaTeX_Caligraphic-Regular.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Caligraphic-Regular.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Caligraphic-Regular.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_Fraktur';\n\tsrc: url(/fonts/KaTeX_Fraktur-Bold.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Fraktur-Bold.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Fraktur-Bold.ttf) format('truetype');\n\tfont-weight: bold;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_Fraktur';\n\tsrc: url(/fonts/KaTeX_Fraktur-Regular.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Fraktur-Regular.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Fraktur-Regular.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_Main';\n\tsrc: url(/fonts/KaTeX_Main-Bold.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Main-Bold.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Main-Bold.ttf) format('truetype');\n\tfont-weight: bold;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_Main';\n\tsrc: url(/fonts/KaTeX_Main-BoldItalic.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Main-BoldItalic.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Main-BoldItalic.ttf) format('truetype');\n\tfont-weight: bold;\n\tfont-style: italic;\n}\n@font-face {\n\tfont-family: 'KaTeX_Main';\n\tsrc: url(/fonts/KaTeX_Main-Italic.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Main-Italic.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Main-Italic.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: italic;\n}\n@font-face {\n\tfont-family: 'KaTeX_Main';\n\tsrc: url(/fonts/KaTeX_Main-Regular.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Main-Regular.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Main-Regular.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_Math';\n\tsrc: url(/fonts/KaTeX_Math-BoldItalic.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Math-BoldItalic.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Math-BoldItalic.ttf) format('truetype');\n\tfont-weight: bold;\n\tfont-style: italic;\n}\n@font-face {\n\tfont-family: 'KaTeX_Math';\n\tsrc: url(/fonts/KaTeX_Math-Italic.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Math-Italic.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Math-Italic.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: italic;\n}\n@font-face {\n\tfont-family: 'KaTeX_SansSerif';\n\tsrc: url(/fonts/KaTeX_SansSerif-Bold.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_SansSerif-Bold.woff) format('woff'),\n\t\turl(/fonts/KaTeX_SansSerif-Bold.ttf) format('truetype');\n\tfont-weight: bold;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_SansSerif';\n\tsrc: url(/fonts/KaTeX_SansSerif-Italic.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_SansSerif-Italic.woff) format('woff'),\n\t\turl(/fonts/KaTeX_SansSerif-Italic.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: italic;\n}\n@font-face {\n\tfont-family: 'KaTeX_SansSerif';\n\tsrc: url(/fonts/KaTeX_SansSerif-Regular.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_SansSerif-Regular.woff) format('woff'),\n\t\turl(/fonts/KaTeX_SansSerif-Regular.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_Script';\n\tsrc: url(/fonts/KaTeX_Script-Regular.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Script-Regular.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Script-Regular.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_Size1';\n\tsrc: url(/fonts/KaTeX_Size1-Regular.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Size1-Regular.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Size1-Regular.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_Size2';\n\tsrc: url(/fonts/KaTeX_Size2-Regular.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Size2-Regular.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Size2-Regular.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_Size3';\n\tsrc: url(/fonts/KaTeX_Size3-Regular.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Size3-Regular.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Size3-Regular.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_Size4';\n\tsrc: url(/fonts/KaTeX_Size4-Regular.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Size4-Regular.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Size4-Regular.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: normal;\n}\n@font-face {\n\tfont-family: 'KaTeX_Typewriter';\n\tsrc: url(/fonts/KaTeX_Typewriter-Regular.woff2) format('woff2'),\n\t\turl(/fonts/KaTeX_Typewriter-Regular.woff) format('woff'),\n\t\turl(/fonts/KaTeX_Typewriter-Regular.ttf) format('truetype');\n\tfont-weight: normal;\n\tfont-style: normal;\n}\n";
styleInject(css_248z$4);

var KatexOutput = /*#__PURE__*/function (_React$Component) {
  _inherits(KatexOutput, _React$Component);

  var _super = _createSuper(KatexOutput);

  function KatexOutput(props) {
    var _this;

    _classCallCheck(this, KatexOutput);

    _this = _super.call(this, props);

    _defineProperty(_assertThisInitialized(_this), "handleContainerRef", function (ref) {
      _this.containerRef = ref;
    });

    _this._timer = null;
    return _this;
  }

  _createClass(KatexOutput, [{
    key: "_update",
    value: function _update() {
      var _this2 = this;

      if (this._timer) {
        clearTimeout(this._timer);
      }

      this._timer = setTimeout(function () {
        katex__default["default"].render(_this2.props.content, _this2.containerRef, {
          displayMode: true
        });
      }, 0);
    }
  }, {
    key: "componentDidMount",
    value: function componentDidMount() {
      this._update();
    }
  }, {
    key: "componentWillReceiveProps",
    value: function componentWillReceiveProps(nextProps) {
      if (nextProps.content !== this.props.content) {
        this._update();
      }
    }
  }, {
    key: "componentWillUnmount",
    value: function componentWillUnmount() {
      clearTimeout(this._timer);
      this._timer = null;
    }
  }, {
    key: "render",
    value: function render() {
      var Component = 'div';

      if (this.props.inline) {
        Component = 'span';
      }

      return /*#__PURE__*/React__default["default"].createElement(Component, {
        contentEditable: this.props.contentEditable,
        className: "".concat(this.props.inline ? 'inline-katex-wrapper' : ''),
        ref: this.handleContainerRef,
        onClick: this.props.onClick
      });
    }
  }]);

  return KatexOutput;
}(React__default["default"].Component);

var TeXBlock = /*#__PURE__*/function (_React$Component2) {
  _inherits(TeXBlock, _React$Component2);

  var _super2 = _createSuper(TeXBlock);

  function TeXBlock(props) {
    var _this3;

    _classCallCheck(this, TeXBlock);

    _this3 = _super2.call(this, props);
    _this3.state = {
      editMode: false
    };

    _this3._onClick = function () {
      if (_this3.state.editMode) {
        return;
      }

      _this3.setState({
        editMode: true,
        texValue: _this3._getValue()
      }, function () {
        _this3._startEdit();
      });
    };

    _this3._onValueChange = function (evt) {
      var value = evt.target.value;
      var invalid = false;

      try {
        katex__default["default"].__parse(value);
      } catch (e) {
        invalid = true;
      } finally {
        _this3.setState({
          invalidTeX: invalid,
          texValue: value
        });
      }
    };

    _this3._save = function () {
      var entityKey = _this3.props.block.getEntityAt(0);

      var newContentState = _this3.props.contentState.mergeEntityData(entityKey, {
        content: _this3.state.texValue
      });

      _this3.setState({
        invalidTeX: false,
        editMode: false,
        texValue: null
      }, _this3._finishEdit.bind(_assertThisInitialized(_this3), newContentState));
    };

    _this3._remove = function () {
      _this3.props.blockProps.onRemove(_this3.props.block.getKey());
    };

    _this3._startEdit = function () {
      _this3.props.blockProps.onStartEdit(_this3.props.block.getKey());
    };

    _this3._finishEdit = function (newContentState) {
      _this3.props.blockProps.onFinishEdit(_this3.props.block.getKey(), newContentState);
    };

    return _this3;
  }

  _createClass(TeXBlock, [{
    key: "_getValue",
    value: function _getValue() {
      return this.props.contentState.getEntity(this.props.block.getEntityAt(0)).getData()['content'];
    }
  }, {
    key: "render",
    value: function render() {
      var texContent = null;
      var readOnly = this.props.blockProps.readOnly;

      if (this.state.editMode) {
        if (this.state.invalidTeX) {
          texContent = '';
        } else {
          texContent = this.state.texValue;
        }
      } else {
        texContent = this._getValue();
      }

      var className = 'TeXEditor-tex';

      if (this.state.editMode) {
        className += ' TeXEditor-activeTeX';
      }

      var editPanel = null;

      if (this.state.editMode) {
        var buttonClass = 'TeXEditor-saveButton';

        if (this.state.invalidTeX) {
          buttonClass += ' TeXEditor-invalidButton';
        }

        editPanel = /*#__PURE__*/React__default["default"].createElement("div", {
          className: "TeXEditor-panel"
        }, /*#__PURE__*/React__default["default"].createElement("textarea", {
          className: "TeXEditor-texValue",
          onChange: this._onValueChange,
          value: this.state.texValue
        }), /*#__PURE__*/React__default["default"].createElement("div", {
          className: "TeXEditor-buttons"
        }, /*#__PURE__*/React__default["default"].createElement("button", {
          className: buttonClass,
          disabled: this.state.invalidTeX,
          onClick: this._save
        }, this.state.invalidTeX ? 'Invalid TeX' : 'Done'), /*#__PURE__*/React__default["default"].createElement("button", {
          className: "TeXEditor-removeButton",
          onClick: this._remove
        }, "Remove")));
      }

      return /*#__PURE__*/React__default["default"].createElement("div", {
        className: className,
        style: {
          cursor: readOnly ? 'default' : ''
        }
      }, /*#__PURE__*/React__default["default"].createElement(KatexOutput, {
        content: texContent,
        onClick: readOnly ? undefined : this._onClick
      }), editPanel);
    }
  }]);

  return TeXBlock;
}(React__default["default"].Component);

var css_248z$3 = ".pe-spinner,\n.pe-spinner:after {\n\tborder-radius: 50%;\n\twidth: 24px;\n\theight: 24px;\n}\n.pe-spinner {\n\tdisplay: block;\n\tmargin: 10px auto;\n\tfont-size: 10px;\n\tposition: relative;\n\ttext-indent: -9999em;\n\tborder-top: 2px solid rgba(47, 46, 46, 0.2);\n\tborder-right: 2px solid rgba(47, 46, 46, 0.2);\n\tborder-bottom: 2px solid rgba(47, 46, 46, 0.2);\n\tborder-left: 2px solid #000;\n\t-webkit-transform: translateZ(0);\n\t-ms-transform: translateZ(0);\n\ttransform: translateZ(0);\n\t-webkit-animation: pe-spinner-animation 1.1s infinite linear;\n\tanimation: pe-spinner-animation 1.1s infinite linear;\n}\n@-webkit-keyframes pe-spinner-animation {\n\t0% {\n\t\t-webkit-transform: rotate(0deg);\n\t\ttransform: rotate(0deg);\n\t}\n\t100% {\n\t\t-webkit-transform: rotate(360deg);\n\t\ttransform: rotate(360deg);\n\t}\n}\n@keyframes pe-spinner-animation {\n\t0% {\n\t\t-webkit-transform: rotate(0deg);\n\t\ttransform: rotate(0deg);\n\t}\n\t100% {\n\t\t-webkit-transform: rotate(360deg);\n\t\ttransform: rotate(360deg);\n\t}\n}\n\n.pe-try-again-button {\n\tborder: solid 1px;\n\tcolor: #2196f3;\n\tbackground: white;\n\theight: 32px;\n\tpadding: 0 16px;\n\tborder-radius: 4px;\n\tmargin-top: 8px;\n\tcursor: pointer;\n}\n";
styleInject(css_248z$3);

var Spin = function Spin() {
  return /*#__PURE__*/React__default["default"].createElement("span", {
    className: "pe-spinner"
  });
};

var Button$1 = function Button(props) {
  return /*#__PURE__*/React__default["default"].createElement("button", _extends({
    className: "pe-try-again-button"
  }, props));
};

var Image = /*#__PURE__*/function (_React$Component) {
  _inherits(Image, _React$Component);

  var _super = _createSuper(Image);

  function Image(props, context) {
    var _this;

    _classCallCheck(this, Image);

    _this = _super.call(this, props, context);

    _defineProperty(_assertThisInitialized(_this), "handleError", function (e) {
      _this.setState({
        isLoading: false,
        hasError: true
      });

      if (_this.state.imageKey < 5) {
        _this.timeoutId = setTimeout(function () {
          _this.setState({
            imageKey: _this.state.imageKey + 1,
            hasError: false,
            isLoading: true
          });
        }, 5000 * _this.state.imageKey);
      }
    });

    _defineProperty(_assertThisInitialized(_this), "handleOnLoad", function (e) {
      _this.setState({
        isLoading: false,
        isLoaded: true,
        hasError: false
      });
    });

    _defineProperty(_assertThisInitialized(_this), "retryNow", function (e) {
      clearTimeout(_this.timeoutId);

      _this.setState({
        imageKey: _this.state.imageKey + 1,
        hasError: false,
        isLoading: true
      });
    });

    _this.state = {
      imageKey: 1,
      isLoading: true,
      hasError: false
    };
    return _this;
  }

  _createClass(Image, [{
    key: "render",
    value: function render() {
      var url = this.props.src;
      var _this$state = this.state,
          isLoading = _this$state.isLoading,
          hasError = _this$state.hasError;
      return /*#__PURE__*/React__default["default"].createElement("div", {
        style: {
          textAlign: 'center'
        }
      }, /*#__PURE__*/React__default["default"].createElement("div", null, url ? /*#__PURE__*/React__default["default"].createElement(React__default["default"].Fragment, null, /*#__PURE__*/React__default["default"].createElement("img", {
        key: this.state.imageKey,
        onError: this.handleError,
        onLoad: this.handleOnLoad,
        alt: "",
        style: {
          maxWidth: '100%'
        },
        src: url
      }), isLoading ? /*#__PURE__*/React__default["default"].createElement("div", null, /*#__PURE__*/React__default["default"].createElement(Spin, null), /*#__PURE__*/React__default["default"].createElement("div", null, "Loading")) : null, hasError ? /*#__PURE__*/React__default["default"].createElement("div", null, /*#__PURE__*/React__default["default"].createElement("div", null, "An error occurred while loading image. Please check your internet and try again."), /*#__PURE__*/React__default["default"].createElement(Button$1, {
        onClick: this.retryNow
      }, "Try again")) : null) : /*#__PURE__*/React__default["default"].createElement("span", null, "Image not available")));
    }
  }]);

  return Image;
}(React__default["default"].Component);

React__default["default"].useEffect;
    React__default["default"].useRef;
    React__default["default"].useState;

function getUrl(data) {
  if (_typeof(data) === 'object') {
    return data['url'];
  }
}

var ImageBlock = /*#__PURE__*/function (_React$Component) {
  _inherits(ImageBlock, _React$Component);

  var _super = _createSuper(ImageBlock);

  function ImageBlock(props, context) {
    var _this;

    _classCallCheck(this, ImageBlock);

    _this = _super.call(this, props, context);

    _defineProperty(_assertThisInitialized(_this), "handleClick", function (e) {
      if (_this.state.editMode) {
        return;
      }

      _this.setState({
        editMode: true,
        url: _this.props.contentState.getEntity(_this.props.block.getEntityAt(0)).getData()['url']
      }, _this.startEdit);
    });

    _defineProperty(_assertThisInitialized(_this), "finishEdit", function (newContentState) {
      _this.props.blockProps.onFinishEdit(_this.props.block.getKey(), newContentState);
    });

    _defineProperty(_assertThisInitialized(_this), "startEdit", function () {
      _this.props.blockProps.onStartEdit(_this.props.block.getKey());
    });

    _defineProperty(_assertThisInitialized(_this), "handleSaveClick", function (e) {
      if (_this.file) {
        _this.uploadImage(_this.file);
      }
    });

    _defineProperty(_assertThisInitialized(_this), "save", function (url) {
      var entityKey = _this.props.block.getEntityAt(0);

      var newContentState = _this.props.contentState.mergeEntityData(entityKey, {
        url: url,
        file: undefined
      });

      _this.setState({
        editMode: false,
        url: null
      }, _this.finishEdit.bind(_assertThisInitialized(_this), newContentState));
    });

    _defineProperty(_assertThisInitialized(_this), "cancel", function (e) {
      _this.setState({
        editMode: false,
        url: null
      }, function () {
        return _this.finishEdit(_this.props.contentState);
      });
    });

    _defineProperty(_assertThisInitialized(_this), "remove", function (e) {
      _this.props.blockProps.onRemove(_this.props.block.getKey());
    });

    _defineProperty(_assertThisInitialized(_this), "handleFileChange", function (e) {
      _this.file = e.target.files && e.target.files[0] ? e.target.files[0] : null;

      if (_this.file) {
        _this.handleSaveClick();
      }
    });

    _defineProperty(_assertThisInitialized(_this), "randomName", function () {
      function makeid() {
        var text = '';
        var possible = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';

        for (var i = 0; i < 5; i++) {
          text += possible.charAt(Math.floor(Math.random() * possible.length));
        }

        return text;
      }

      return makeid() + Date.now();
    });

    _defineProperty(_assertThisInitialized(_this), "uploadImage", function (file) {
      var getImagePolicy = _this.props.blockProps.getImagePolicy;

      _this.setState({
        isUploading: true
      });

      setTimeout(function () {
        getImagePolicy(file).then(function (_ref) {
          var policy = _ref.policy,
              success = _ref.success;

          if (success) {
            var fullURL = policy.url + '/' + policy.fields.key;
            var formData = new FormData();
            Object.keys(policy.fields).forEach(function (key) {
              var value = policy.fields[key];
              formData.append(key, value);
            });
            formData.append('file', file);
            fetch(policy.url, {
              method: 'POST',
              headers: {},
              body: formData
            }).then(function () {
              _this.save(fullURL);

              _this.setState({
                isUploading: false
              });
            });
          } else {
            _this.setState({
              isUploading: false
            });

            alert('Some error occurred while uploading image');
          }
        })["catch"](function (error) {
          _this.setState({
            isUploading: false
          });

          console.log("error occurred", error);
        });
      }, [2000]); // this.reader.readAsDataURL(file)
    });

    _defineProperty(_assertThisInitialized(_this), "handleRef", function (ref) {
      _this.inputRef = ref;
    });

    var editMode = !props.contentState.getEntity(_this.props.block.getEntityAt(0)).getData()['url'];
    _this.fileToUpload = props.contentState.getEntity(_this.props.block.getEntityAt(0)).getData().file;

    if (_this.fileToUpload) {
      editMode = false;
    }

    _this.state = {
      editMode: editMode,
      image: '',
      uploadOnMount: !!_this.fileToUpload
    };
    return _this;
  }

  _createClass(ImageBlock, [{
    key: "componentDidMount",
    value: function componentDidMount() {
      if (this.state.editMode) {
        this.inputRef && this.inputRef.click();
      }

      if (this.state.uploadOnMount) {
        this.uploadImage(this.fileToUpload);
      }

      var self = this;
      this.reader = new FileReader();
      this.reader.addEventListener('load', function (result) {
        self.save(result.srcElement['result']);
      }, false);
    }
  }, {
    key: "render",
    value: function render() {
      var _this$state = this.state,
          editMode = _this$state.editMode,
          isUploading = _this$state.isUploading;
      var _this$props$blockProp = this.props.blockProps,
          readOnly = _this$props$blockProp.readOnly,
          transformUrl = _this$props$blockProp.transformUrl;
      var url;

      if (editMode) {
        url = this.state.url;
      } else {
        var data = this.props.contentState.getEntity(this.props.block.getEntityAt(0)).getData();
        url = getUrl(data);

        if (typeof transformUrl === 'function') {
          url = transformUrl(url);
        }
      }

      if (readOnly) {
        return /*#__PURE__*/React__default["default"].createElement(Image, {
          src: url
        });
      }

      return /*#__PURE__*/React__default["default"].createElement("div", {
        onClick: readOnly ? undefined : this.handleClick,
        style: {
          cursor: 'default',
          textAlign: 'center'
        }
      }, editMode ? /*#__PURE__*/React__default["default"].createElement("div", null, /*#__PURE__*/React__default["default"].createElement("div", null, "Click here to upload image", /*#__PURE__*/React__default["default"].createElement("input", {
        ref: this.handleRef,
        onChange: this.handleFileChange,
        type: "file",
        accept: "image/*"
      })), /*#__PURE__*/React__default["default"].createElement("div", null, /*#__PURE__*/React__default["default"].createElement("button", {
        disabled: isUploading,
        onClick: this.handleSaveClick
      }, isUploading ? 'Saving...' : 'Save'), /*#__PURE__*/React__default["default"].createElement("button", {
        onClick: this.cancel
      }, "Cancel"), /*#__PURE__*/React__default["default"].createElement("button", {
        onClick: this.remove
      }, "Remove"))) : null, /*#__PURE__*/React__default["default"].createElement("div", null, url ? /*#__PURE__*/React__default["default"].createElement("img", {
        src: url
      }) : /*#__PURE__*/React__default["default"].createElement("span", null, "No image uploaded")));
    }
  }]);

  return ImageBlock;
}(React__default["default"].Component);

var AtomicBlockUtils$1 = Draft__default["default"].AtomicBlockUtils,
    EditorState$5 = Draft__default["default"].EditorState;
var count = 0;
var examples = ['\\int_a^bu\\frac{d^2v}{dx^2}\\,dx\n' + '=\\left.u\\frac{dv}{dx}\\right|_a^b\n' + '-\\int_a^b\\frac{du}{dx}\\frac{dv}{dx}\\,dx', 'P(E) = {n \\choose k} p^k (1-p)^{ n-k} ', '\\tilde f(\\omega)=\\frac{1}{2\\pi}\n' + '\\int_{-\\infty}^\\infty f(x)e^{-i\\omega x}\\,dx', '\\frac{1}{(\\sqrt{\\phi \\sqrt{5}}-\\phi) e^{\\frac25 \\pi}} =\n' + '1+\\frac{e^{-2\\pi}} {1+\\frac{e^{-4\\pi}} {1+\\frac{e^{-6\\pi}}\n' + '{1+\\frac{e^{-8\\pi}} {1+\\ldots} } } }'];
function insertTeXBlock(editorState, formula) {
  var contentState = editorState.getCurrentContent();
  var nextFormula = count++ % examples.length;
  var contentStateWithEntity = contentState.createEntity('TOKEN', 'IMMUTABLE', {
    content: formula || examples[nextFormula]
  });
  var entityKey = contentStateWithEntity.getLastCreatedEntityKey();
  var newEditorState = EditorState$5.set(editorState, {
    currentContent: contentStateWithEntity
  });
  return AtomicBlockUtils$1.insertAtomicBlock(newEditorState, entityKey, ' ');
}

var EditorState$4 = Draft__default["default"].EditorState,
    Modifier$3 = Draft__default["default"].Modifier,
    SelectionState$1 = Draft__default["default"].SelectionState;
function removeTeXBlock(editorState, blockKey) {
  var content = editorState.getCurrentContent();
  var block = content.getBlockForKey(blockKey);
  var targetRange = new SelectionState$1({
    anchorKey: blockKey,
    anchorOffset: 0,
    focusKey: blockKey,
    focusOffset: block.getLength()
  });
  var withoutTeX = Modifier$3.removeRange(content, targetRange, 'backward');
  var resetBlock = Modifier$3.setBlockType(withoutTeX, withoutTeX.getSelectionAfter(), 'unstyled');
  var newState = EditorState$4.push(editorState, resetBlock, 'remove-range');
  return EditorState$4.forceSelection(newState, resetBlock.getSelectionAfter());
}

var Modifier$2 = Draft__default["default"].Modifier,
    EditorState$3 = Draft__default["default"].EditorState;
function insertText(editorState, content) {
  var selectionState = editorState.getSelection();
  var contentState = editorState.getCurrentContent();
  var contentStateWithLink = Modifier$2.replaceText(contentState, selectionState, content);
  var newEditorState = EditorState$3.push(editorState, contentStateWithLink, 'insert-characters');
  return newEditorState;
}

var Modifier$1 = Draft__default["default"].Modifier,
    EditorState$2 = Draft__default["default"].EditorState;
var INLINE_EQUATION = 'ie';
function insertInlineEquation(editorState) {
  var selectionState = editorState.getSelection();
  var contentState = editorState.getCurrentContent();
  var contentStateWithEntity = contentState.createEntity(INLINE_EQUATION, 'IMMUTABLE', {
    content: 'Hello World!'
  });
  var entityKey = contentStateWithEntity.getLastCreatedEntityKey();
  var contentStateWithLink = Modifier$1.applyEntity(contentStateWithEntity, selectionState, entityKey);
  var newEditorState = EditorState$2.push(editorState, contentStateWithLink, 'apply-entity');
  return newEditorState;
}

var AtomicBlockUtils = Draft__default["default"].AtomicBlockUtils,
    EditorState$1 = Draft__default["default"].EditorState;
function insertImageBlock(editorState, file) {
  var contentState = editorState.getCurrentContent();
  var contentStateWithEntity = contentState.createEntity('IMAGE', 'IMMUTABLE', {
    url: null,
    file: file
  });
  var entityKey = contentStateWithEntity.getLastCreatedEntityKey();
  var newEditorState = EditorState$1.set(editorState, {
    currentContent: contentStateWithEntity
  });
  return AtomicBlockUtils.insertAtomicBlock(newEditorState, entityKey, ' ');
}

var PrpeleafEditorGlobalContext = /*#__PURE__*/React__default["default"].createContext({
  readOnly: false,
  changeText: function changeText() {}
});

var css_248z$2 = ".inline-equation-display-wrapper .editable {\n\tposition: relative;\n}\n\n.inline-equation-display-wrapper:hover .inline-equation-popover {\n\tdisplay: inline;\n}\n\n.inline-equation-popover {\n\tposition: absolute;\n\tbottom: 90%;\n\tleft: 0;\n\tz-index: 5;\n\tbackground: white;\n\tpadding: 8px 12px;\n\tborder: solid 1px #333;\n\tcursor: pointer;\n\tdisplay: none;\n}\n\n.pe-portal-root {\n\tposition: fixed;\n\ttop: 0px;\n\tleft: 0px;\n\tright: 0px;\n\tbottom: 0px;\n\tz-index: 999999999;\n\tbackground-color: rgba(0, 0, 0, 0.4);\n\tbackdrop-filter: blur(3px) opacity(0.7);\n}\n\n.pe-portal-cntn {\n\tposition: absolute;\n\ttop: 0px;\n\tleft: 0px;\n\tright: 0px;\n\tbottom: 0px;\n\tz-index: 5;\n\tmargin: auto;\n\toverflow: auto;\n}\n\n.pe-portal-cntrhlpr {\n\tdisplay: flex;\n\t-webkit-box-pack: center;\n\tjustify-content: center;\n\tposition: relative;\n\tpadding-top: 10%;\n\tmargin: auto auto 4%;\n}\n\n.pe-portal-styler {\n\tmin-width: 400px;\n\twidth: 100%;\n\tmax-width: 800px;\n\tbackground-color: #fff;\n\tbox-shadow: rgba(0, 0, 0, 0.13) 2px 4px 19px 0px;\n\tborder-radius: 8px;\n\tpadding: 24px;\n}\n\n.pe-portal-textarea {\n\twidth: 100%;\n\tborder: solid 1px #888;\n\tborder-radius: 8px;\n\tpadding: 12px;\n}\n.pe-portal-button {\n\tbox-shadow: none;\n\toutline: none;\n\tborder: solid 1px;\n\theight: 32px;\n\tpadding: 0 12px;\n\tborder-radius: 4px;\n\tmargin: 4px;\n\tcursor: pointer;\n}\n\n.pe-portal-button.submit {\n\tbackground: #1976d2;\n\tborder-color: #1976d2;\n\tcolor: white;\n}\n\n.pe-portal-button.cancel {\n\tbackground-color: white;\n\tcolor: #333;\n}\n\n.pe-portal-error {\n\tcolor: red;\n\ttext-align: center;\n}\n";
styleInject(css_248z$2);

var inlineEquationRegex$1 = /\$(.*?)\$/g;
var EditEquation = /*#__PURE__*/function (_React$Component) {
  _inherits(EditEquation, _React$Component);

  var _super = _createSuper(EditEquation);

  function EditEquation(props, context) {
    var _this;

    _classCallCheck(this, EditEquation);

    _this = _super.call(this, props, context);

    _defineProperty(_assertThisInitialized(_this), "setValue", function (value) {
      _this.setState({
        value: value,
        isValid: _this.validate(value, false)
      });
    });

    _defineProperty(_assertThisInitialized(_this), "handleSubmit", function () {
      _this.props.onChange('$' + _this.state.value + '$');
    });

    var _value = props.value ? props.value.substring(1, props.value.length - 1) : '';

    _this.state = {
      isValid: _this.validate(_value),
      value: _value
    };
    return _this;
  }

  _createClass(EditEquation, [{
    key: "validate",
    value: function validate() {
      var value = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : '';
      var invalid = false;

      try {
        katex__default["default"].__parse(value);
      } catch (e) {
        invalid = true;
      } finally {
        return !invalid;
      }
    }
  }, {
    key: "render",
    value: function render() {
      var _this$props = this.props,
          onCancel = _this$props.onCancel;
          _this$props.onChange;
          _this$props.value;
      var setValue = this.setValue;
      var _this$state = this.state,
          value = _this$state.value,
          isValid = _this$state.isValid;
      var content = /*#__PURE__*/React__default["default"].createElement("div", {
        className: "pe-portal-root"
      }, /*#__PURE__*/React__default["default"].createElement("div", {
        className: "pe-portal-cntn"
      }, /*#__PURE__*/React__default["default"].createElement("div", {
        className: "pe-portal-cntrhlpr"
      }, /*#__PURE__*/React__default["default"].createElement("div", {
        className: "pe-portal-styler"
      }, /*#__PURE__*/React__default["default"].createElement("textarea", {
        className: "pe-portal-textarea",
        onFocus: function onFocus(e) {
          return e.stopPropagation();
        },
        onBlur: function onBlur(e) {
          return e.stopPropagation();
        },
        type: "text",
        value: value,
        onChange: function onChange(e) {
          return setValue(e.target.value);
        }
      }), isValid ? /*#__PURE__*/React__default["default"].createElement(KatexOutput, {
        content: value
      }) : /*#__PURE__*/React__default["default"].createElement("div", {
        className: "pe-portal-error"
      }, "Invalid Equation"), /*#__PURE__*/React__default["default"].createElement("button", {
        className: "pe-portal-button cancel",
        onClick: onCancel
      }, "Cancel"), /*#__PURE__*/React__default["default"].createElement("button", {
        className: "pe-portal-button submit",
        onClick: this.handleSubmit
      }, "Change")))));
      return content;
    }
  }]);

  return EditEquation;
}(React__default["default"].Component);

function findWithRegex$1(regex, contentBlock, callback) {
  var text = contentBlock.getText();
  var matchArr, start;

  while ((matchArr = regex.exec(text)) !== null) {
    start = matchArr.index;
    callback(start, start + matchArr[0].length);
  }
}

var strategy$1 = function strategy(contentBlock, callback, contentState) {
  return findWithRegex$1(new RegExp(inlineEquationRegex$1), contentBlock, callback);
};

var InlineEquation$1 = /*#__PURE__*/function (_React$Component2) {
  _inherits(InlineEquation, _React$Component2);

  var _super2 = _createSuper(InlineEquation);

  function InlineEquation(props, context) {
    var _this2;

    _classCallCheck(this, InlineEquation);

    _this2 = _super2.call(this, props, context);

    _defineProperty(_assertThisInitialized(_this2), "setIsEditing", function (isEditing) {
      _this2.setState({
        isEditing: isEditing
      });
    });

    _this2.state = {
      isEditing: false
    };
    return _this2;
  }

  _createClass(InlineEquation, [{
    key: "render",
    value: function render() {
      var _this$props2 = this.props,
          blockKey = _this$props2.blockKey;
          _this$props2.contentState;
          var decoratedText = _this$props2.decoratedText,
          children = _this$props2.children,
          start = _this$props2.start,
          end = _this$props2.end;
      this.state.isEditing;
      this.setIsEditing;
      var _this$context = this.context,
          readOnly = _this$context.readOnly,
          openInlineEquationEditor = _this$context.openInlineEquationEditor,
          changeText = _this$context.changeText;
      var matchResult = new RegExp(inlineEquationRegex$1).exec(decoratedText);
      matchResult && matchResult[1];
      var katexDisplay = /*#__PURE__*/React__default["default"].createElement(KatexOutput, {
        inline: true,
        content: decoratedText.substring(1, decoratedText.length - 1)
      });
      return /*#__PURE__*/React__default["default"].createElement("span", {
        style: {
          backgroundColor: '',
          display: 'inline-block'
        }
      }, readOnly ? katexDisplay : /*#__PURE__*/React__default["default"].createElement("span", {
        className: 'inline-equation-display-wrapper' + (readOnly ? ' readonly' : ' editable')
      }, katexDisplay, readOnly ? null : /*#__PURE__*/React__default["default"].createElement("div", {
        className: "inline-equation-popover"
      }, /*#__PURE__*/React__default["default"].createElement("button", {
        onClick: function onClick(e) {
          e.stopPropagation();
          e.preventDefault();
          openInlineEquationEditor(blockKey, start, end, decoratedText);
        },
        className: "inline-equation-popover-button"
      }, "Edit"), /*#__PURE__*/React__default["default"].createElement("button", {
        onClick: function onClick(e) {
          e.stopPropagation();
          e.preventDefault();
          changeText(blockKey, start, end, '');
        },
        className: "inline-equation-popover-button"
      }, "Remove"))), /*#__PURE__*/React__default["default"].createElement("span", {
        style: {
          width: '0',
          height: 0,
          overflow: 'hidden',
          display: 'inline-block'
        }
      }, children));
    }
  }]);

  return InlineEquation;
}(React__default["default"].Component);

_defineProperty(InlineEquation$1, "contextType", PrpeleafEditorGlobalContext);

var inlineEquationDecorator = {
  strategy: strategy$1,
  component: InlineEquation$1
};

var css_248z$1 = ".prepleaf-editor-inline-highlighted-text {\n\tbackground-color: #000;\n\tcolor: #fff;\n\tpadding: 0 3px;\n\tmargin: 0 3px;\n\tdisplay: inline-block;\n}\n";
styleInject(css_248z$1);

var inlineEquationRegex = /\[\[(.*?)\]\]/g;
/*#__PURE__*/(function (_React$Component) {
  _inherits(EditEquation, _React$Component);

  var _super = _createSuper(EditEquation);

  function EditEquation(props, context) {
    var _this;

    _classCallCheck(this, EditEquation);

    _this = _super.call(this, props, context);

    _defineProperty(_assertThisInitialized(_this), "setValue", function (value) {
      _this.setState({
        value: value,
        isValid: _this.validate(value, false)
      });
    });

    _defineProperty(_assertThisInitialized(_this), "handleSubmit", function () {
      _this.props.onChange('[[' + _this.state.value + ']]');
    });

    var _value = props.value ? props.value.substring(1, props.value.length - 1) : '';

    _this.state = {
      isValid: _this.validate(_value),
      value: _value
    };
    return _this;
  }

  _createClass(EditEquation, [{
    key: "validate",
    value: function validate() {
      var value = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : '';
      var invalid = false;

      try {
        katex.__parse(value);
      } catch (e) {
        invalid = true;
      } finally {
        return !invalid;
      }
    }
  }, {
    key: "render",
    value: function render() {
      var _this$props = this.props,
          onCancel = _this$props.onCancel;
          _this$props.onChange;
          _this$props.value;
      var setValue = this.setValue;
      var _this$state = this.state,
          value = _this$state.value,
          isValid = _this$state.isValid;
      var content = /*#__PURE__*/React__default["default"].createElement("div", {
        className: "pe-portal-root"
      }, /*#__PURE__*/React__default["default"].createElement("div", {
        className: "pe-portal-cntn"
      }, /*#__PURE__*/React__default["default"].createElement("div", {
        className: "pe-portal-cntrhlpr"
      }, /*#__PURE__*/React__default["default"].createElement("div", {
        className: "pe-portal-styler"
      }, /*#__PURE__*/React__default["default"].createElement("textarea", {
        className: "pe-portal-textarea",
        onFocus: function onFocus(e) {
          return e.stopPropagation();
        },
        onBlur: function onBlur(e) {
          return e.stopPropagation();
        },
        type: "text",
        value: value,
        onChange: function onChange(e) {
          return setValue(e.target.value);
        }
      }), isValid ? /*#__PURE__*/React__default["default"].createElement("span", {
        style: {
          padding: '0 3px',
          backgroundColor: '#000'
        }
      }, value) : /*#__PURE__*/React__default["default"].createElement("div", {
        className: "pe-portal-error"
      }, "Invalid Equation"), /*#__PURE__*/React__default["default"].createElement("button", {
        className: "pe-portal-button cancel",
        onClick: onCancel
      }, "Cancel"), /*#__PURE__*/React__default["default"].createElement("button", {
        className: "pe-portal-button submit",
        onClick: this.handleSubmit
      }, "Change")))));
      return content;
    }
  }]);

  return EditEquation;
})(React__default["default"].Component);

function findWithRegex(regex, contentBlock, callback) {
  var text = contentBlock.getText();
  var matchArr, start;

  while ((matchArr = regex.exec(text)) !== null) {
    start = matchArr.index;
    callback(start, start + matchArr[0].length);
  }
}

var strategy = function strategy(contentBlock, callback, contentState) {
  return findWithRegex(new RegExp(inlineEquationRegex), contentBlock, callback);
};

var InlineHighlightedText = /*#__PURE__*/function (_React$Component2) {
  _inherits(InlineHighlightedText, _React$Component2);

  var _super2 = _createSuper(InlineHighlightedText);

  function InlineHighlightedText() {
    _classCallCheck(this, InlineHighlightedText);

    return _super2.apply(this, arguments);
  }

  _createClass(InlineHighlightedText, [{
    key: "render",
    value: function render() {
      var _this$props2 = this.props,
          decoratedText = _this$props2.decoratedText,
          children = _this$props2.children;
      var readOnly = this.context.readOnly;
      var matchResult = new RegExp(inlineEquationRegex).exec(decoratedText);
      var matchedText = matchResult && matchResult[1];
      return /*#__PURE__*/React__default["default"].createElement("span", {
        style: {
          backgroundColor: '',
          display: 'inline-block'
        }
      }, /*#__PURE__*/React__default["default"].createElement("span", {
        className: 'prepleaf-editor-inline-highlighted-text' + (readOnly ? ' readonly' : ' editable')
      }, matchedText), /*#__PURE__*/React__default["default"].createElement("span", {
        style: {
          width: '0',
          height: 0,
          overflow: 'hidden',
          display: 'inline-block'
        }
      }, children));
    }
  }]);

  return InlineHighlightedText;
}(React__default["default"].Component);

_defineProperty(InlineHighlightedText, "contextType", PrpeleafEditorGlobalContext);

var inlineHighlightedTextDecorator = {
  strategy: strategy,
  component: InlineHighlightedText
};

var CompositeDecorator = Draft__default["default"].CompositeDecorator;
var compositeDecorator = new CompositeDecorator([inlineEquationDecorator, inlineHighlightedTextDecorator]);

var InlineEquation = function InlineEquation() {
  return /*#__PURE__*/React__default["default"].createElement("span", null, "Hello");
};

var Button = function Button(props) {
  return /*#__PURE__*/React__default["default"].createElement("button", _extends({
    tabIndex: -1
  }, props));
};

var css_248z = ".prepleaf-editor {\n\tdisplay: flex;\n\tflex-direction: column;\n\tflex: 1;\n\talign-items: center;\n\tmargin: 5px auto;\n}\n\n.prepleaf-editor *:after,\n.prepleaf-editor *:before,\n.prepleaf-editor *,\n.prepleaf-editor {\n\tbox-sizing: border-box;\n}\n\n.TeXEditor-toolbar {\n\tdisplay: flex;\n\twidth: 100%;\n\tborder-left: solid 1px #999;\n\tborder-top: solid 1px #999;\n\tborder-right: solid 1px #999;\n\tjustify-content: space-between;\n}\n\n.TeXEditor-toolbar .TeXEditor-toolbar-list {\n\tdisplay: flex;\n}\n.TeXEditor-insert-button {\n\tborder: none;\n\tcolor: #333;\n\tpadding: 8px 16px;\n\tborder-right: solid 1px #999;\n}\n.TeXEditor-insert-button.hidden {\n\tdisplay: none;\n}\n\n.TeXEditor-root {\n\tfont-family: 'Century Schoolbook', serif;\n\t-webkit-font-smoothing: antialiased;\n\tmargin: 0 auto;\n\tflex: 1;\n\twidth: 100%;\n}\n\n.TeXEditor-editor {\n\tcursor: text;\n\tfont-size: 18px;\n\tmin-height: 40px;\n\tpadding: 5px;\n}\n\n.TeXEditor-button {\n\tmargin-top: 10px;\n\ttext-align: center;\n}\n\n.TeXEditor-handle {\n\tcolor: rgba(98, 177, 254, 1);\n\tdirection: ltr;\n\tunicode-bidi: bidi-override;\n}\n\n.TeXEditor-hashtag {\n\tcolor: rgba(95, 184, 138, 1);\n}\n\n.TeXEditor-tex {\n\tbackground-color: #fff;\n\tcursor: pointer;\n\tmargin: 0px auto;\n\tpadding: 0px;\n\t-webkit-transition: background-color 0.2s fade-in-out;\n\tuser-select: none;\n\t-webkit-user-select: none;\n}\n\n.TeXEditor-activeTeX {\n\tcolor: #888;\n}\n\n.TeXEditor-panel {\n\tfont-family: 'Helvetica', sans-serif;\n\tfont-weight: 200;\n}\n\n.TeXEditor-panel .TeXEditor-texValue {\n\tborder: 1px solid #e1e1e1;\n\tdisplay: block;\n\tfont-family: 'Inconsolata', 'Menlo', monospace;\n\tfont-size: 14px;\n\theight: 110px;\n\tmargin: 20px auto 10px;\n\toutline: none;\n\tpadding: 14px;\n\tresize: none;\n\t-webkit-box-sizing: border-box;\n\twidth: 500px;\n}\n\n.TeXEditor-buttons {\n\ttext-align: center;\n}\n\n.TeXEditor-saveButton,\n.TeXEditor-removeButton {\n\tbackground-color: #fff;\n\tborder: 1px solid #0a0;\n\tcursor: pointer;\n\tfont-family: 'Helvetica', 'Arial', sans-serif;\n\tfont-size: 16px;\n\tfont-weight: 200;\n\tmargin: 10px auto;\n\tpadding: 6px;\n\t-webkit-border-radius: 3px;\n\twidth: 100px;\n}\n\n.TeXEditor-removeButton {\n\tborder-color: #aaa;\n\tcolor: #999;\n\tmargin-left: 8px;\n}\n\n.TeXEditor-invalidButton {\n\tbackground-color: #eee;\n\tborder-color: #a00;\n\tcolor: #666;\n}\n\n.TeXEditor-insert {\n\tbackground-color: #f1f1f1;\n\tborder: 1px solid #ccc;\n\tborder-radius: 3px;\n\tmargin-left: 5px;\n}\n\n.inline-katex-wrapper .katex-display {\n\tdisplay: inline-block;\n\tmargin-top: 4px;\n\tmargin-bottom: 4px;\n}\n";
styleInject(css_248z);

var Editor = Draft__default["default"].Editor,
    EditorState = Draft__default["default"].EditorState,
    convertFromRaw = Draft__default["default"].convertFromRaw,
    convertToRaw = Draft__default["default"].convertToRaw,
    RichUtils = Draft__default["default"].RichUtils,
    getDefaultKeyBinding = Draft__default["default"].getDefaultKeyBinding,
    KeyBindingUtil = Draft__default["default"].KeyBindingUtil,
    SelectionState = Draft__default["default"].SelectionState,
    Modifier = Draft__default["default"].Modifier;
var hasCommandModifier = KeyBindingUtil.hasCommandModifier;
var Map = immutable.Map;
var customStyleMap = {
  "super": {
    verticalAlign: 'super',
    fontSize: '.8rem'
  },
  sub: {
    verticalAlign: 'sub',
    fontSize: '0.8rem'
  },
  equation: {
    marginLeft: '1px',
    marginRight: '1px',
    fontStyle: 'italic'
  }
};

var keyBindingFn = function keyBindingFn(e) {
  if (e.keyCode === 120) {
    return 'insert_image';
  }

  if (hasCommandModifier(e)) {
    if (e.keyCode === 188) {
      e.preventDefault();
      return 'sub';
    }

    if (e.keyCode === 190) {
      e.preventDefault();
      return 'super';
    }

    if (e.keyCode === 69) {
      e.preventDefault();
      return 'equation';
    }
  }

  return getDefaultKeyBinding(e);
};

var TeXEditor = /*#__PURE__*/function (_React$Component) {
  _inherits(TeXEditor, _React$Component);

  var _super = _createSuper(TeXEditor);

  function TeXEditor(props, context) {
    var _this;

    _classCallCheck(this, TeXEditor);

    _this = _super.call(this, props, context);

    _defineProperty(_assertThisInitialized(_this), "markAsInlineEquation", function () {
      _this.setState({
        editorState: insertInlineEquation(_this.state.editorState)
      });
    });

    _defineProperty(_assertThisInitialized(_this), "toggleSuper", function (e) {
      e.preventDefault();
      e.stopPropagation();
      var editorState = _this.state.editorState;

      _this._toggleName(editorState, 'super');
    });

    _defineProperty(_assertThisInitialized(_this), "toggleSub", function () {
      var editorState = _this.state.editorState;

      _this._toggleName(editorState, 'sub');
    });

    _defineProperty(_assertThisInitialized(_this), "toggleEquation", function () {
      var editorState = _this.state.editorState;

      _this._toggleName(editorState, 'equation');
    });

    _defineProperty(_assertThisInitialized(_this), "_insertImage", function () {
      _this.setState({
        imageEdits: Map(),
        editorState: insertImageBlock(_this.state.editorState)
      });
    });

    _defineProperty(_assertThisInitialized(_this), "_blockRenderer", function (block) {
      var _this$props = _this.props,
          getImagePolicy = _this$props.getImagePolicy,
          readOnly = _this$props.readOnly,
          transformImageUrl = _this$props.transformImageUrl;

      if (block.getType() === 'atomic') {
        var contentState = _this.state.editorState.getCurrentContent();

        var type = contentState.getEntity(block.getEntityAt(0)).getType();

        if (type === 'TOKEN') {
          return {
            component: TeXBlock,
            editable: false,
            props: {
              onStartEdit: function onStartEdit(blockKey) {
                var liveTeXEdits = _this.state.liveTeXEdits;

                _this.setState({
                  liveTeXEdits: liveTeXEdits.set(blockKey, true)
                });
              },
              onFinishEdit: function onFinishEdit(blockKey, newContentState) {
                var liveTeXEdits = _this.state.liveTeXEdits;

                _this.setState({
                  liveTeXEdits: liveTeXEdits.remove(blockKey),
                  editorState: EditorState.createWithContent(newContentState, compositeDecorator)
                });
              },
              onRemove: function onRemove(blockKey) {
                return _this._removeTeX(blockKey);
              },
              readOnly: readOnly
            }
          };
        }

        if (type === 'IMAGE') {
          return {
            component: ImageBlock,
            editable: false,
            props: {
              onStartEdit: function onStartEdit(blockKey) {
                var imageEdits = _this.state.imageEdits;

                _this.setState({
                  imageEdits: imageEdits.set(blockKey, true)
                });
              },
              onFinishEdit: function onFinishEdit(blockKey, newContentState) {
                var imageEdits = _this.state.imageEdits;

                _this.setState({
                  imageEdits: imageEdits.remove(blockKey),
                  editorState: EditorState.createWithContent(newContentState, compositeDecorator)
                });
              },
              onRemove: function onRemove(blockKey) {
                return _this._removeTeX(blockKey);
              },
              getImagePolicy: getImagePolicy,
              readOnly: readOnly,
              transformUrl: transformImageUrl
            }
          };
        }

        if (type === INLINE_EQUATION) {
          return {
            component: InlineEquation
          };
        }
      } else if (block.getType() === 'unstyled') ;

      return null;
    });

    _defineProperty(_assertThisInitialized(_this), "refreshPasteEquationFlag", function () {
      if (window.localStorage.getItem('pasteEquationFlag') === 'inline') {
        _this.setState({
          pasteEquationInline: true
        });
      } else {
        _this.setState({
          pasteEquationInline: false
        });
      }
    });

    _defineProperty(_assertThisInitialized(_this), "handlePasteEquationFlagChange", function (e) {
      window.localStorage.setItem('pasteEquationFlag', e.target.checked ? 'inline' : 'block');

      _this.refreshPasteEquationFlag();
    });

    _defineProperty(_assertThisInitialized(_this), "changeText", function (blockKey, start, end, text) {
      var editorState = _this.state.editorState;
      var emptySelection = SelectionState.createEmpty(blockKey);
      var selection = emptySelection.merge({
        anchorOffset: start,
        focusOffset: end
      });
      var newContentState = Modifier.replaceText(editorState.getCurrentContent(), selection, text);
      var newEditorState = EditorState.createWithContent(newContentState, compositeDecorator);

      _this.setState({
        editorState: newEditorState,
        editInlineEquation: undefined
      });
    });

    _defineProperty(_assertThisInitialized(_this), "handleEditorRef", function (ref) {
      _this.editorRef = ref;
    });

    var rawContent = props.rawContent;
    var contentEditorState; // loadKatexCSS();

    if (typeof rawContent === 'undefined') {
      contentEditorState = EditorState.createEmpty(compositeDecorator);
    } else {
      var modifiedRawContent;

      if (_typeof(rawContent) === 'object') {
        modifiedRawContent = _objectSpread2({
          entityMap: {},
          blocks: []
        }, rawContent);
      } else {
        modifiedRawContent = _objectSpread2({
          entityMap: {},
          blocks: []
        }, JSON.parse(rawContent));
      }

      contentEditorState = EditorState.createWithContent(convertFromRaw(modifiedRawContent), compositeDecorator);
    }

    _this.state = {
      editorState: contentEditorState,
      liveTeXEdits: Map(),
      imageEdits: Map(),
      pasteEquationInline: false
    };

    _this._focus = function () {
      return _this.editorRef.focus();
    };

    _this._onChange = function (editorState) {
      _this.setState({
        editorState: editorState
      });

      if (_this.props.onChange) {
        _this.props.onChange(_this.value);
      }
    };

    _this._toggleName = function (editorState, name) {
      _this._onChange(RichUtils.toggleInlineStyle(editorState, name));
    };

    _this._handleKeyCommand = function (command, editorState) {
      if (['super', 'sub'].indexOf(command) > -1) {
        _this._toggleName(editorState, command);

        return true;
      }

      if ('equation' === command) {
        _this.markAsInlineEquation();
      }

      if ('insert_image' === command) {
        _this._insertImage();
      }

      var newState = RichUtils.handleKeyCommand(editorState, command);

      if (newState) {
        _this._onChange(newState);

        return true;
      }

      return false;
    };

    _this._removeTeX = function (blockKey) {
      var _this$state = _this.state,
          editorState = _this$state.editorState,
          liveTeXEdits = _this$state.liveTeXEdits,
          imageEdits = _this$state.imageEdits;

      _this.setState({
        liveTeXEdits: liveTeXEdits.remove(blockKey),
        imageEdits: imageEdits.remove(blockKey),
        editorState: removeTeXBlock(editorState, blockKey)
      });
    };

    _this._insertTeX = function () {
      _this.setState({
        liveTeXEdits: Map(),
        editorState: insertTeXBlock(_this.state.editorState)
      });
    };

    return _this;
  }

  _createClass(TeXEditor, [{
    key: "value",
    get: function get() {
      var editorState = this.state.editorState;
      return {
        rawContent: convertToRaw(editorState.getCurrentContent())
      };
    }
  }, {
    key: "resetEditor",
    value: function resetEditor() {
      var contentEditorState = EditorState.createEmpty(compositeDecorator);
      this.setState({
        editorState: contentEditorState,
        liveTeXEdits: Map()
      });
    }
  }, {
    key: "componentDidMount",
    value: function componentDidMount() {
      var customRef = this.props.customRef;
      customRef && customRef(this);
      this.refreshPasteEquationFlag();
    }
  }, {
    key: "componentWillUnmount",
    value: function componentWillUnmount() {
      var customRef = this.props.customRef;
      customRef && customRef(null);
    }
  }, {
    key: "contextValue",
    get: function get() {
      var _this2 = this;

      return {
        openInlineEquationEditor: function openInlineEquationEditor(blockKey, start, end, text) {
          _this2.setState({
            editInlineEquation: {
              blockKey: blockKey,
              start: start,
              end: end,
              text: text
            }
          });
        },
        changeText: this.changeText,
        readOnly: this.props.readOnly
      };
    }
  }, {
    key: "render",
    value:
    /**
     * While editing TeX, set the Draft editor to read-only. This allows us to
     * have a textarea within the DOM.
     */
    function render() {
      var _this3 = this;

      var readOnly = this.props.readOnly;
      var pasteEquationInline = this.state.pasteEquationInline;

      if (readOnly) {
        return /*#__PURE__*/React__default["default"].createElement("div", null, /*#__PURE__*/React__default["default"].createElement(PrpeleafEditorGlobalContext.Provider, {
          value: this.contextValue
        }, /*#__PURE__*/React__default["default"].createElement(Editor, {
          customStyleMap: customStyleMap,
          blockRendererFn: this._blockRenderer,
          editorState: this.state.editorState,
          handleKeyCommand: this._handleKeyCommand,
          keyBindingFn: keyBindingFn,
          onChange: this._onChange,
          readOnly: readOnly || this.state.liveTeXEdits.count() || this.state.imageEdits.count(),
          ref: this.handleEditorRef,
          spellCheck: true
        })));
      }

      return /*#__PURE__*/React__default["default"].createElement("div", {
        className: "prepleaf-editor"
      }, /*#__PURE__*/React__default["default"].createElement("div", {
        className: "TeXEditor-toolbar"
      }, /*#__PURE__*/React__default["default"].createElement("div", {
        className: "TeXEditor-toolbar-list"
      }, /*#__PURE__*/React__default["default"].createElement(Button, {
        onMouseDown: this.toggleEquation,
        className: "TeXEditor-insert-button hidden"
      }, "inline equation"), /*#__PURE__*/React__default["default"].createElement(Button, {
        onMouseDown: this.toggleSub,
        className: "TeXEditor-insert-button"
      }, "X", /*#__PURE__*/React__default["default"].createElement("sub", null, "2")), /*#__PURE__*/React__default["default"].createElement(Button, {
        onMouseDown: this.toggleSuper,
        className: "TeXEditor-insert-button"
      }, "X", /*#__PURE__*/React__default["default"].createElement("sup", null, "2")), /*#__PURE__*/React__default["default"].createElement(Button, {
        onMouseDown: this._insertTeX,
        className: "TeXEditor-insert-button"
      }, "Equation"), /*#__PURE__*/React__default["default"].createElement(Button, {
        onMouseDown: this._insertImage,
        className: "TeXEditor-insert-button"
      }, "Image")), /*#__PURE__*/React__default["default"].createElement("div", null, this.state.editInlineEquation ? /*#__PURE__*/React__default["default"].createElement(EditEquation, {
        value: this.state.editInlineEquation.text,
        onCancel: function onCancel() {
          return _this3.setState({
            editInlineEquation: undefined
          });
        },
        onChange: function onChange(text) {
          _this3.changeText(_this3.state.editInlineEquation.blockKey, _this3.state.editInlineEquation.start, _this3.state.editInlineEquation.end, text);
        }
      }) : null, /*#__PURE__*/React__default["default"].createElement("div", {
        style: {}
      }, /*#__PURE__*/React__default["default"].createElement("label", null, /*#__PURE__*/React__default["default"].createElement("input", {
        checked: pasteEquationInline,
        onChange: this.handlePasteEquationFlagChange,
        type: "checkbox"
      }), "Paste Equation Inline")), /*#__PURE__*/React__default["default"].createElement("div", {
        style: {
          display: 'none'
        }
      }, "For inline eqn use $equatoin in here$: $\\frac", '{2}{3}$'))), /*#__PURE__*/React__default["default"].createElement("div", {
        className: "TeXEditor-root"
      }, /*#__PURE__*/React__default["default"].createElement("div", {
        className: "TeXEditor-editor",
        style: {
          border: 'solid 1px #777'
        },
        onClick: this._focus
      }, /*#__PURE__*/React__default["default"].createElement(PrpeleafEditorGlobalContext.Provider, {
        value: this.contextValue
      }, /*#__PURE__*/React__default["default"].createElement(Editor, {
        handlePastedFiles: function handlePastedFiles(files) {
          var editorState = _this3.state.editorState;

          _this3.setState({
            editorState: insertImageBlock(editorState, files[0])
          });

          return 'handled';
        },
        handleDroppedFiles: function handleDroppedFiles(selection, files) {
          var updatedSelectionEditorState = EditorState.acceptSelection(_this3.state.editorState, selection);

          _this3.setState({
            editorState: insertImageBlock(updatedSelectionEditorState, files[0])
          });

          return 'handled';
        },
        handlePastedText: function handlePastedText(text, html, editorState) {
          if (text.indexOf('$$') === 0 && text.substring(text.length - 2)) {
            if (pasteEquationInline) {
              var newEditorState = insertText(editorState, text.substring(1, text.length - 1) + ' ');

              _this3.setState({
                editorState: newEditorState
              });

              return 'handled';
            }

            var content = text.substring(2, text.length - 2);

            _this3.setState({
              editorState: insertTeXBlock(editorState, content)
            });

            return 'handled';
          }

          return 'not-handled';
        },
        customStyleMap: customStyleMap,
        blockRendererFn: this._blockRenderer,
        editorState: this.state.editorState,
        handleKeyCommand: this._handleKeyCommand,
        keyBindingFn: keyBindingFn,
        onChange: this._onChange,
        placeholder: "Start a document...",
        readOnly: readOnly || this.state.liveTeXEdits.count() || this.state.imageEdits.count(),
        ref: this.handleEditorRef,
        spellCheck: true
      })))));
    }
  }]);

  return TeXEditor;
}(React__default["default"].Component);
TeXEditor.propTypes = {
  readOnly: PropTypes.bool.isRequired,
  getImageUrl: PropTypes.func
};
TeXEditor.defaultProps = {
  readOnly: false
};

var PrepleafEditor = /*#__PURE__*/function (_React$Component) {
  _inherits(PrepleafEditor, _React$Component);

  var _super = _createSuper(PrepleafEditor);

  function PrepleafEditor() {
    _classCallCheck(this, PrepleafEditor);

    return _super.apply(this, arguments);
  }

  _createClass(PrepleafEditor, [{
    key: "render",
    value: function render() {
      return /*#__PURE__*/React__default["default"].createElement(TeXEditor, this.props);
    }
  }]);

  return PrepleafEditor;
}(React__default["default"].Component);

PrepleafEditor.propTypes = {
  readOnly: PropTypes.bool.isRequired,
  onChange: PropTypes.func
};
PrepleafEditor.defaultProps = {
  readOnly: false
};

module.exports = PrepleafEditor;
