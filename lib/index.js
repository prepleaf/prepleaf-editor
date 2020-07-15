'use strict';

if (process.env.NODE_ENV === 'production') {
	module.exports = require('./prepleaf-editor.min.js');
} else {
	module.exports = require('./prepleaf-editor.js');
}
