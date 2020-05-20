import resolve from '@rollup/plugin-node-resolve';
import babel from 'rollup-plugin-babel';
import commonjs from '@rollup/plugin-commonjs';
import livereload from 'rollup-plugin-livereload';
import { terser } from 'rollup-plugin-terser';
import injectProcessEnv from 'rollup-plugin-inject-process-env';
import postcss from 'rollup-plugin-postcss';
import * as DraftJS from 'draft-js';
import * as immutablejs from 'immutable';

export default {
	input: 'src/index.js',
	output: {
		file: 'lib/index.js',
		format: 'cjs',
	},
	plugins: [
		resolve(),
		babel({
			exclude: 'node_modules/**', // only transpile our source code
		}),
		postcss({
			plugins: [],
		}),
		commonjs({
			namedExports: {
				'draft-js': Object.keys(DraftJS),
				immutable: Object.keys(immutablejs),
			},
		}),
		injectProcessEnv({
			NODE_ENV: 'development',
		}),
		// When we're building for production (npm run build
		// instead of npm run dev), minify
		terser(),
	],
	external: ['react'],
};
