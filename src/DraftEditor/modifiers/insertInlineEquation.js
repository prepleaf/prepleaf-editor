import { Modifier, EditorState, convertToRaw } from 'draft-js';

let count = 0;
export const INLINE_EQUATION = 'ie';

export function insertInlineEquation(editorState) {
	const selectionState = editorState.getSelection();
	const contentState = editorState.getCurrentContent();
	const contentStateWithEntity = contentState.createEntity(
		INLINE_EQUATION,
		'IMMUTABLE',
		{ content: 'Hello Wprld!' }
	);
	const entityKey = contentStateWithEntity.getLastCreatedEntityKey();
	const contentStateWithLink = Modifier.applyEntity(
		contentStateWithEntity,
		selectionState,
		entityKey
	);

	// const newEditorState = EditorState.set(editorState, {
	// 	currentContent: contentStateWithEntity,
	// });
	const newEditorState = EditorState.push(
		editorState,
		contentStateWithLink,
		'apply-entity'
	);
	return newEditorState;
}
