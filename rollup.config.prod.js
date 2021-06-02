import resolve from '@rollup/plugin-node-resolve';
import babel from 'rollup-plugin-babel';
import commonjs from '@rollup/plugin-commonjs';
import { terser } from 'rollup-plugin-terser';
import postcss from 'rollup-plugin-postcss';
import * as DraftJS from 'draft-js';
import * as immutablejs from 'immutable';
import * as React from 'react';

export default [
	{
		input: 'src/index.js',
		output: {
			file: 'lib/prepleaf-editor.js',
			format: 'cjs',
		},
		plugins: [
			resolve(),
			babel({ exclude: 'node_modules/**' }),
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
		],
		external: ['react', 'react-dom', 'katex', 'draft-js'],
	},
	{
		input: 'lib/prepleaf-editor.js',
		output: {
			file: 'lib/prepleaf-editor.min.js',
			format: 'cjs',
		},
		plugins: [
			// When we're building for production (npm run build
			// instead of npm run dev), minify
			terser(),
		],
	},
];
