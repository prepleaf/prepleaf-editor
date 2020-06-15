import { Modifier, EditorState, convertToRaw } from 'draft-js';

let count = 0;
export const INLINE_EQUATION = 'ie';

export function insertText(editorState, content) {
	console.log(content);
	const selectionState = editorState.getSelection();
	const contentState = editorState.getCurrentContent();
	// const contentStateWithEntity = contentState.createEntity(
	// 	'unstyled',
	// 	'MUTABLE',
	// 	{ content }
	// );
	// const entityKey = contentStateWithEntity.getLastCreatedEntityKey();
	const contentStateWithLink = Modifier.replaceText(
		contentState,
		selectionState,
		content
	);

	const newEditorState = EditorState.push(
		editorState,
		contentStateWithLink,
		'insert-characters'
	);
	return newEditorState;
}
