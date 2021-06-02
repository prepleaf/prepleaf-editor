import Draft from 'draft-js';

const { AtomicBlockUtils, EditorState } = Draft;

export function insertImageBlock(editorState, file) {
	const contentState = editorState.getCurrentContent();
	const contentStateWithEntity = contentState.createEntity(
		'IMAGE',
		'IMMUTABLE',
		{ url: null, file }
	);
	const entityKey = contentStateWithEntity.getLastCreatedEntityKey();
	const newEditorState = EditorState.set(editorState, {
		currentContent: contentStateWithEntity,
	});
	return AtomicBlockUtils.insertAtomicBlock(newEditorState, entityKey, ' ');
}
