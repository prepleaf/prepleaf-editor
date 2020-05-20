import { AtomicBlockUtils, EditorState } from 'draft-js';

let count = 0;
const examples = [
	'\\int_a^bu\\frac{d^2v}{dx^2}\\,dx\n' +
		'=\\left.u\\frac{dv}{dx}\\right|_a^b\n' +
		'-\\int_a^b\\frac{du}{dx}\\frac{dv}{dx}\\,dx',

	'P(E) = {n \\choose k} p^k (1-p)^{ n-k} ',

	'\\tilde f(\\omega)=\\frac{1}{2\\pi}\n' +
		'\\int_{-\\infty}^\\infty f(x)e^{-i\\omega x}\\,dx',

	'\\frac{1}{(\\sqrt{\\phi \\sqrt{5}}-\\phi) e^{\\frac25 \\pi}} =\n' +
		'1+\\frac{e^{-2\\pi}} {1+\\frac{e^{-4\\pi}} {1+\\frac{e^{-6\\pi}}\n' +
		'{1+\\frac{e^{-8\\pi}} {1+\\ldots} } } }',
];

export function insertTeXBlock(editorState) {
	const contentState = editorState.getCurrentContent();
	const nextFormula = count++ % examples.length;
	const contentStateWithEntity = contentState.createEntity(
		'TOKEN',
		'IMMUTABLE',
		{ content: examples[nextFormula] }
	);
	const entityKey = contentStateWithEntity.getLastCreatedEntityKey();
	const newEditorState = EditorState.set(editorState, {
		currentContent: contentStateWithEntity,
	});
	return AtomicBlockUtils.insertAtomicBlock(newEditorState, entityKey, ' ');
}
