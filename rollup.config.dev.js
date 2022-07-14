import resolve from '@rollup/plugin-node-resolve';
import babel from '@rollup/plugin-babel';
import commonjs from '@rollup/plugin-commonjs';
import livereload from 'rollup-plugin-livereload';
import injectProcessEnv from 'rollup-plugin-inject-process-env';
import postcss from 'rollup-plugin-postcss';
import * as DraftJS from 'draft-js';
import * as immutablejs from 'immutable';
// import * as React from 'react';

// console.log(Object.keys(React));

export default {
	input: 'examples/index.js',
	output: {
		file: 'examples/build/bundle.js',
		format: 'cjs',
	},
	plugins: [
		resolve(),
		babel({
			exclude: 'node_modules/**', // only transpile our source code
			babelHelpers: 'bundled',
		}),
		commonjs({
			transformMixedEsModules: true,
			esmExternals: true,
			defaultIsModuleExports: true,
			// namedExports: {
			// 'draft-js': Object.keys(DraftJS),
			// immutable: Object.keys(immutablejs),
			// react: Object.keys(React),
			// },
		}),
		postcss({
			plugins: [],
		}),
		injectProcessEnv({
			NODE_ENV: 'development',
		}),
		serve(),

		// Watch the `public` directory and refresh the
		// browser on changes when not in production
		livereload('examples'),

		// If we're building for production (npm run build
		// instead of npm run dev), minify
	],
	external: [],
};

function serve() {
	let started = false;

	return {
		writeBundle() {
			if (!started) {
				started = true;

				require('child_process').spawn('npm', ['run', 'start', '--', '--dev'], {
					stdio: ['ignore', 'inherit', 'inherit'],
					shell: true,
				});
			}
		},
	};
}
